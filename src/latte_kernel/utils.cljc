(ns latte-kernel.utils
 "A set of dummy utilities.")

(defn vconcat
  "Concatenates vectors `v1` and `v2`.
  (linear time)."
  [v1 v2]
  (loop [s v2, v v1]
    (if (seq s)
      (recur (rest s) (conj v (first s)))
      v)))

(defn vcons
  "Conses element `e` in front of vector `v`.
   (linear time)"
  [e v]
  (vconcat [e] v))

(defn pair?
  "Is `v` a pair?"
  [v]
  (and (vector v)
       (= (count v) 2)))

(defn vectorn?
  "Is `v` a vector of size a multiple of `n`?"
  [v n]
  (and (vector v)
       (= (rem (count v) n) 0)))

(defn safe-get
  "A safe(r) variant of `get` for collections with non-`nil` keys."
  [coll key]
  (if-let [val (get coll key)]
    val
    (throw (ex-info "No such value is collection" {:coll coll :key key}))))

(defn nano-time []
  "Fetch the current time (with high precision).
Returns 0 in clojurescript."
  #?(:clj (System/nanoTime)
     :cljs 0))

(defn zip
  "Zip a sequence of even-numbered elements to a sequence of pairs,
i.e. (zip '(x1 y2 x2 y2 ...)) = ([x1 y1] [x2 y2] ...)"
  [s]
  (if (seq s)
    (if (seq (rest s))
      (lazy-seq (cons [(first s) (first (rest s))] (zip (rest (rest s)))))
      (throw (ex-info "Cannot zip sequence with odd number of elements." {:seq s})))
    s))

(defn vremove [pred v]
  "Remove all elements recognizing `pred` in vector `v`."
  (into [] (remove pred v)))
