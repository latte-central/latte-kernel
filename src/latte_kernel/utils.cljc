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

(def vector*
  "Creates a new vector containing the items prepended to the rest, the last
  of which will be treated as a sequence."
  (comp vec list*))

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
    (throw (ex-info "No such value in collection" {:coll coll :key key}))))

(defn nano-time
  "Fetch the current time (with high precision).
  Returns 0 in clojurescript."
  []
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

(defn vremove
  "Remove all elements recognizing `pred` in vector `v`."
  [pred v]
  (vec (remove pred v)))

(defn map-with
  "Combine a mapv of `f` on `coll` with a reduce on `val`.
  `f` should be a function of two arguments and return a couple.
  It will be applied on `val` and the first element in `coll`, then on the first
  part of the returning couple and the second element in `coll`, etc...
  Return a couple with the resulting `val` and a vector containing all elements
  in `coll` with `f` applied to them."
  [f val coll]
  (loop [s coll, val val, res []]
    (if (seq s)
      (let [[val' x] (f val (first s))]
        (recur (rest s) val' (conj res x)))
      [val, res])))
