(ns latte-kernel.defenv
  "The definitional environment.")

;;{
;; # Definitional entities

;; This namespace provides the underlying structures for
;; representing the main LaTTe abstractions: definitions,
;; theorems, axioms, notations, etc.
;;}

;;{
;; ## Definition

;; Mathematical definitions are encoded as named, parameterized
;; lambda-terms.
;;}

(defrecord Definition [name params arity parsed-term type])

;;{
;; The components of a definition are:
;;   - the `name` of the defined term
;;   - the vector `params` of typed parameters
;;   - the `arity` of the definition, i.e. its number of parameters
;;   - the `parsed-term` corresponding to the body of the definition
;;   - the `type` of the defined lambda-term.
;;}

(defn definition? [v]
  (instance? Definition v))

;;{
;; ## Theorem

;; A theorem is the assertion of a type inhabitation.

;;}

(defrecord Theorem [name params arity type proof])

;;{
;; The components of a theorem are:
;;   - its `name`
;;   - the vector `params` of the typed parameters
;;   - the `arity` of the theorem, i.e. its number of parameters
;;   - the asserted `type`
;;   - the `proof` of the theorem, i.e. a lambda-term or
;;  a script (for building the proof term) that inhabits the
;;  asserted type.

;; A theorem can only be used if the `proof` component is
;; set to a non-`nil` value.
;;}

(defn theorem? [v]
  (instance? Theorem v))

;;{
;; ## Axiom

;; An axiom is like a theorem accepted without a proof.
;; It is of a primary mathematical importance to limit
;; the number of axioms to rely on. But it is impossible
;; to develop any mathematical content without some
;; underlying axioms.
;;}

(defrecord Axiom [name params arity type])

;;{
;; The main difference with `Theorem` is that there is
;; of course no `proof` component.
;;}

(defn axiom? [v]
  (instance? Axiom v))

;;{
;; ## Notation

;; A notation is an expression that is expanded to a
;; lambda-term at parsing time.
;;
;; **Remark** : It is the objective
;; of LaTTe *not* to rely on complex notations, but
;; some constructs, e.g. existentials benefit from
;; some syntactic sugar provided by notations.
;;}

(comment

(defrecord Notation [name notation-fn])

;; somewhat hacky but "safe"
(defn- mk-args [n]
  (vec (repeat n nil)))

;; courtesy of #whocaresanyway@stackoverflow
(defn- arg-count [f]
  (let [m (first (.getDeclaredMethods (class f)))
        p (.getParameterTypes m)]
    (alength p)))

(defn- dummy-call [f]
  (let [n (arg-count f)]
    (apply f (mk-args n))))

(defn get-notation-fn [f]
  (:notation-fn (dummy-call f)))

(defn notation? [v]
  (and (fn? v)
       (instance? Notation (dummy-call v))))

(defrecord Special [name special-fn])

(defn special? [v]
  (instance? Special v))


(defn latte-definition? [v]
  (or (definition? v)
      (theorem? v)
      (axiom? v)
      (notation? v)
      (special? v)))

;;{
;; ## Definitional environment
;;}

(defn fetch-definition [locals sym]
  ;; (println "[fetch-definition] sym=" sym "(type" (type sym) ")")
  (cond
    (symbol? sym) (if-let [ldef (get locals sym)]
                    [:ok ldef]
                    (if-let [symvar (resolve sym)]
                      (recur locals symvar)
                      [:ko {:msg "No such (local) definition" :def sym}]))
    (var? sym) (let [gdef @sym]
                 ;;(println "[fetch-definition] " gdef)
                 [:ok gdef])
    :else (throw (ex-info "Cannot fetch definition (please report)"
                          {:sym sym}))))

(defn registered-definition? [locals sym]
  (let [[status _] (fetch-definition locals sym)]
    (= status :ok)))

(defn qualify-def [locals sym]
  (if (var? sym)
    sym
    (do
      (when (not (symbol? sym))
        (throw (ex-info "Value to qualify should be a var or a symbol (please report)" {:sym sym :type (type sym)})))
      (if-let [_ (get locals sym)]
        sym
        (resolve sym)))))

)
