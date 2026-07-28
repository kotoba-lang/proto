(ns proto.wire
  "Protocol Buffers **wire format** — the bytes, not the schema.

  `proto.core` compiles a schema-as-data into `.proto` source text. This
  namespace is the other half: it reads and writes the encoded bytes, as a
  total function from data to data with no host interop at all.

  ## Why this exists in this shape

  It was written for signature verification, and that requirement drives the
  whole design. Protocols like Storj's sign a message by serializing it,
  signing those bytes, and putting the signature in a field of the same
  message. To *check* such a signature you must remove the signature field and
  reproduce the remaining bytes **exactly** — not equivalently, exactly. A
  decoder that drops fields it does not recognise, or that re-encodes varints
  in its own canonical form, silently produces different bytes and every
  signature fails to verify with no clue as to why.

  So `decode` is lossless. Each field keeps `:raw`, the exact byte slice it
  occupied *including its tag*, and `encode` concatenates those slices. Round
  tripping is byte-identical by construction rather than by care, unknown
  fields survive, and a non-canonical varint written by some other
  implementation comes back out exactly as it went in. Dropping one field and
  re-encoding — which is the whole verification move — is `remove-field`
  followed by `encode`.

  ## Representation

  Bytes are seqs of unsigned ints 0-255 in and out, matching the convention
  the rest of this workspace's portable `.cljc` uses (see `sigv4.core`). No
  `byte-array`, no `Uint8Array`, no reader conditionals: this file is identical
  on every runtime in the kotoba-lang ladder.

  A decoded message is a **vector of field maps** in wire order, not a map
  keyed by field number, because protobuf permits repeated occurrences of the
  same field number and their order is significant.

      {:field-number 2
       :wire-type    :length-delimited
       :value        (104 105)   ; payload only — no tag, no length prefix
       :raw          (18 2 104 105)}

  Interpretation (which field number means what) belongs to the caller; this
  namespace never guesses. See `varint-value`, `bytes->utf8` and friends for
  turning `:value` into something meaningful once you know the schema.

  Spec: https://protobuf.dev/programming-guides/encoding/"
  (:refer-clojure :exclude [bytes]))

;; ── wire types ───────────────────────────────────────────────────────────────
;;
;; 3 and 4 (start-group / end-group) are proto2 groups, deprecated since 2008
;; and absent from every schema this workspace touches. They are rejected
;; rather than silently mis-parsed: a group body is not length-prefixed, so a
;; decoder that does not understand them cannot find the end of the field, and
;; guessing would desynchronise the rest of the message.

(def wire-types
  {0 :varint
   1 :fixed64
   2 :length-delimited
   5 :fixed32})

(def wire-type-codes
  (into {} (map (fn [[k v]] [v k])) wire-types))

(defn- fail [msg data]
  (throw (ex-info (str "proto.wire: " msg) data)))

;; ── varints ──────────────────────────────────────────────────────────────────

(defn- byte-at [v i]
  (bit-and (nth v i) 0xff))

(defn read-varint
  "Read a base-128 varint from `v` (an indexed byte collection) at `offset`.

  Returns `{:value n :length k}`. `:length` is the number of bytes consumed,
  which is not necessarily the number a canonical encoder would have used —
  that is the point, and why callers that must re-emit use `:raw` instead of
  re-encoding `:value`.

  Values are accumulated with `+`/`*` rather than bit ops so the result stays
  correct past 32 bits on ClojureScript, where bitwise operators truncate to
  int32. Beyond 2^53 a JS double cannot hold an integer exactly, so this
  refuses rather than returning a quietly wrong number; callers needing full
  int64 range should read the raw bytes."
  [v offset]
  (loop [i offset, shift 1, acc 0, n 0]
    (when (>= i (count v))
      (fail "truncated varint" {:offset offset}))
    (when (> n 9)
      (fail "varint longer than 10 bytes" {:offset offset}))
    (let [b    (byte-at v i)
          acc' (+ acc (* (bit-and b 0x7f) shift))]
      (when (> acc' 9007199254740991)
        (fail "varint exceeds the exactly-representable integer range"
              {:offset offset}))
      (if (zero? (bit-and b 0x80))
        {:value acc' :length (inc (- i offset))}
        (recur (inc i) (* shift 128) acc' (inc n))))))

(defn write-varint
  "Canonical base-128 varint encoding of a non-negative integer."
  [n]
  (when (or (neg? n) (> n 9007199254740991))
    (fail "varint out of range" {:n n}))
  (loop [n n, out []]
    (if (< n 128)
      (conj out n)
      (recur (quot n 128) (conj out (bit-or 0x80 (mod n 128)))))))

(defn zigzag-decode
  "ZigZag decoding, for `sint32`/`sint64` fields."
  [n]
  (let [half (quot n 2)]
    (if (odd? n) (- (- half) 1) half)))

(defn zigzag-encode
  "ZigZag encoding, for `sint32`/`sint64` fields."
  [n]
  (if (neg? n) (dec (* 2 (- n))) (* 2 n)))

;; ── decode ───────────────────────────────────────────────────────────────────

(defn- decode-field [v offset]
  (let [{tag :value tag-len :length} (read-varint v offset)
        code      (bit-and tag 0x07)
        number    (quot tag 8)
        wire-type (wire-types code)
        body      (+ offset tag-len)]
    (when (nil? wire-type)
      (fail (str "unsupported wire type " code
                 (when (#{3 4} code) " (proto2 group — not supported)"))
            {:field-number number :wire-type-code code :offset offset}))
    (when (zero? number)
      (fail "field number 0 is not valid" {:offset offset}))
    (let [[value end]
          (case wire-type
            :varint           (let [{:keys [length]} (read-varint v body)]
                                [(vec (subvec v body (+ body length))) (+ body length)])
            :fixed64          [(vec (subvec v body (+ body 8)))  (+ body 8)]
            :fixed32          [(vec (subvec v body (+ body 4)))  (+ body 4)]
            :length-delimited (let [{len :value ll :length} (read-varint v body)
                                    from (+ body ll)
                                    to   (+ from len)]
                                (when (> to (count v))
                                  (fail "length-delimited field runs past the end of the message"
                                        {:field-number number :declared-length len}))
                                [(vec (subvec v from to)) to]))]
      {:field-number number
       :wire-type    wire-type
       :value        value
       :raw          (vec (subvec v offset end))
       :end          end})))

(defn decode
  "Decode a protobuf message into a vector of field maps, in wire order.

  Lossless: every field carries `:raw`, so `(encode (decode bs))` returns `bs`
  byte for byte — including unknown fields and non-canonical varints."
  [bs]
  (let [v (vec bs)]
    (loop [offset 0, out []]
      (if (>= offset (count v))
        out
        (let [f (decode-field v offset)]
          (recur (:end f) (conj out (dissoc f :end))))))))

;; ── encode ───────────────────────────────────────────────────────────────────

(defn- encode-field [{:keys [field-number wire-type value raw]}]
  (or raw
      (let [code (or (wire-type-codes wire-type)
                     (fail "unknown wire type" {:wire-type wire-type}))
            tag  (write-varint (+ (* field-number 8) code))
            v    (vec value)]
        (case wire-type
          :length-delimited (vec (concat tag (write-varint (count v)) v))
          (vec (concat tag v))))))

(defn encode
  "Encode a vector of field maps back to bytes.

  A field with `:raw` is emitted verbatim — that is what makes decode/encode
  byte-exact. A field built by hand (no `:raw`) is encoded canonically."
  [fields]
  (vec (mapcat encode-field fields)))

;; ── field access ─────────────────────────────────────────────────────────────

(defn fields
  "All fields with `number`, in wire order. Protobuf allows repeats."
  [msg number]
  (filterv #(= number (:field-number %)) msg))

(defn field
  "The last field with `number`, or nil.

  Last, not first: protobuf's rule for a repeated scalar in a non-repeated
  field is that the final occurrence wins."
  [msg number]
  (last (fields msg number)))

(defn remove-field
  "Drop every occurrence of `number`.

  This is the signature-verification move: clear the signature field, re-encode
  the rest byte-exactly, and check the signature over those bytes."
  [msg number]
  (filterv #(not= number (:field-number %)) msg))

(defn varint-value
  "Interpret a `:varint` field's bytes as an unsigned integer."
  [{:keys [wire-type value] :as f}]
  (when f
    (when-not (= :varint wire-type)
      (fail "not a varint field" {:field f}))
    (:value (read-varint (vec value) 0))))

(defn bytes-value
  "A `:length-delimited` field's payload bytes."
  [{:keys [wire-type value] :as f}]
  (when f
    (when-not (= :length-delimited wire-type)
      (fail "not a length-delimited field" {:field f}))
    value))

(defn message-value
  "A `:length-delimited` field decoded as a nested message."
  [f]
  (some-> (bytes-value f) decode))

(defn bytes->utf8
  "Decode UTF-8 bytes to a string. Pure — no TextDecoder, no String
  constructor — so the result is identical on every runtime.

  Malformed input is rejected rather than replaced with U+FFFD: these bytes are
  usually inside something that was signed, and silently substituting a
  replacement character would change a value that a signature covers."
  [bs]
  (let [v (vec bs)
        n (count v)]
    (loop [i 0, out []]
      (if (>= i n)
        (apply str out)
        (let [b (byte-at v i)
              [cp len]
              (cond
                (< b 0x80) [b 1]
                (= 0xc0 (bit-and b 0xe0)) [(bit-and b 0x1f) 2]
                (= 0xe0 (bit-and b 0xf0)) [(bit-and b 0x0f) 3]
                (= 0xf0 (bit-and b 0xf8)) [(bit-and b 0x07) 4]
                :else (fail "invalid UTF-8 lead byte" {:offset i :byte b}))]
          (when (> (+ i len) n)
            (fail "truncated UTF-8 sequence" {:offset i}))
          (let [cp (loop [k 1, cp cp]
                     (if (>= k len)
                       cp
                       (let [c (byte-at v (+ i k))]
                         (when-not (= 0x80 (bit-and c 0xc0))
                           (fail "invalid UTF-8 continuation byte" {:offset (+ i k)}))
                         (recur (inc k) (+ (* cp 64) (bit-and c 0x3f))))))]
            (recur (+ i len)
                   (conj out (if (> cp 0xffff)
                               ;; outside the BMP — surrogate pair
                               (let [c (- cp 0x10000)]
                                 (str (char (+ 0xd800 (quot c 1024)))
                                      (char (+ 0xdc00 (mod c 1024)))))
                               (char cp))))))))))

;; ── construction ─────────────────────────────────────────────────────────────

(defn varint-field
  "A `:varint` field holding `n`."
  [number n]
  {:field-number number :wire-type :varint :value (write-varint n)})

(defn bytes-field
  "A `:length-delimited` field holding raw bytes (also how `string` and
  embedded messages are encoded)."
  [number bs]
  {:field-number number :wire-type :length-delimited :value (vec bs)})

(defn message-field
  "A `:length-delimited` field holding an encoded nested message."
  [number msg]
  (bytes-field number (encode msg)))
