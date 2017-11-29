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

(defrecord Definition [name params arity parsed-term type opts])

;;{
;; The components of a definition are:
;;   - the `name` of the defined term
;;   - the vector `params` of typed parameters
;;   - the `arity` of the definition, i.e. its number of parameters
;;   - the `parsed-term` corresponding to the body of the definition
;;   - the `type` of the defined lambda-term.
;;   - some options may be indicated in the map `opts`.
;;     one particularly useful option is `opaque` which, when true,
;;     avoids any unfolding of the definition (this is useful for
;;     e.g. equality).
;;}

(defn definition?
  "Is `v` a definition?"
  [v]
  (instance? Definition v))

(def empty-env [{} {}])

(defn mkenv [env] [env {}])

(defn local-definitions [env]
(second env))

(defn register-definition
  ([def-env rdef] (register-definition def-env rdef false))
  ([def-env rdef local?]
   (let [[global-defs local-defs] def-env]
     (if local?
       [global-defs (assoc local-defs (:name rdef) rdef)]
       [(assoc global-defs (:name rdef) rdef) local-defs]))))

;;{
;; Definitions are searched by *name*, which can be:
;;   - directly a Clojure or Clojurescript *var*
;;   - indirectly a symbol
;;
;; In the case of Clojurescript, the symbol will be *resolved* to
;; the corresponding var (if any). In Clojurescript, dynamic name
;; resolution is not available.

;; The definitions identified by symbols are searched in an explicit
;; definitional environment. The *vars* are searched in the implicit
;; environment provided by the current namespace.
;;}

(defn fetch-definition
  "Fetches definition named `dname` in priority in the supplied `def-env` map.
  In the Clojure (not Clojurescript) version the definition is also sought in the current namespace.

  If the optional argument `local-only?` is set to `true` then the definition is
 looked for in `def-env` and only for definition tagged \"local\". In any case the current namespace
  is not considered. In Clojurescript the namespace is not considered anyways. The flag is `false` by default."
  ([def-env dname] (fetch-definition def-env dname false))
  ([def-env dname local-only?]
   (let [[global-defs local-defs] def-env]
     ;; (println "[fetch-definition] dname=" dname)
     (cond
       (symbol? dname) (if-let [ldef (get local-defs dname)]
                         [:ok ldef]
                         #?(:clj (if local-only?
                                   [:ko {:msg "No such (local) definition" :def dname}]
                                   (if-let [gdef (get global-defs dname)]
                                     [:ok gdef]
                                     (if-let [dnamevar (resolve dname)]
                                       (recur def-env dnamevar local-only?)
                                       [:ko {:msg "No such (global) definition" :def dname}])))
                            :cljs (if-let [gdef (get global-defs dname)]
                                    [:ok gdef]
                                    [:ko {:msg "No such (global) definition" :def dname}])))
       (var? dname) (let [gdef @dname]
                      ;;(println "[fetch-definition] " gdef)
                      [:ok gdef])
       :else (throw (ex-info "Cannot fetch definition (please report)"
                             {:dname dname}))))))

(defn registered-definition?
  "Does `dname` corresponds to the name of a registered definition
  in `def-env` (or the current namespace)?"
  ([dname] (registered-definition? empty-env dname false))
  ([def-env dname] (registered-definition? def-env dname false))
  ([def-env dname local?]
   (let [[status _] (fetch-definition def-env dname local?)]
     (= status :ok))))

;;{
;; Definition name corresponding to namespace *vars* must be resolved
;; to a fully qualified name.
;; This does not apply to the Clojurescript case since symbol resolution
;; is not available.
;;}

(defn qualify-def [def-env dname]
  (if (var? dname)
    dname
    (do
      (when (not (symbol? dname))
        (throw (ex-info "Value to qualify should be a var or a symbol (please report)" {:dname dname :type (type dname)})))
      (let [[global-defs local-defs] def-env]
        (if-let [_ (get local-defs dname)]
          dname
          (if-let [_ (get global-defs dname)]
            dname
            #?(:clj (let [res-dname (resolve dname)]
                      (if (nil? res-dname)
                        (throw (ex-info "Cannot qualify symbol: not a known definition"
                                        {:symbol dname}))
                        res-dname))
               :cljs (throw (ex-info "Cannot qualify symbol: not a known definition"
                                     {:symbol dname})))))))))

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


(defrecord Notation [name notation-fn])

(defn notation?
  "Is `v` a notation?"
  [v]
  (instance? Notation v))

;;{
;; ## Implicits
;;
;; An *implicit* is a term expanded at typing-time.
;; This is mostly used for programmatically-generated
;; terms, in particular to provide an underlying
;; support for implicit arguments.
;;}

(defrecord Implicit [name implicit-fn])

(defn implicit?
  "Is `v` an implicit?"
  [v]
  (instance? Implicit v))


;;{
;; ## LaTTe definitions
;;
;; As a summary, a LaTTe definition can be:
;;  - a mathematical definition
;;  - a theorem statement
;;  - an axiom statement
;;  - a new notation
;;  - an *implicit*
;;}

(defn latte-definition?
  "Is `v` a LaTTe defining *thing*?"
  [v]
  (or (definition? v)
      (theorem? v)
      (axiom? v)
      (notation? v)
      (implicit? v)))
