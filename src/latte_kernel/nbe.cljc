(ns latte-kernel.nbe
  (:require [latte-kernel.defenv :as defenv :refer [implicit? definition?
                                                    theorem? axiom?]]
            [latte-kernel.syntax :as stx]))

;;{
;; # Normalisation by evaluation
;;
;; Instead of applying ourselves the normalisation as seen in `norm.cljc`,
;; we want to let the Clojure language do for us the complicated part:
;; substituting argument names for their value while respecting nested scopes,
;; aka calling the λ/Π-functions.
;;
;; This is done in three steps:
;; 1. translating λ/Π-expressions into Clojure functions.
;; 2. normalising those terms, aka applying the functions wherever possible.
;; 3. retranslating back into normal λ/Π-terms.
;;
;;The first two steps are done by the `evaluation` function, and the last one
;; is done by `quotation`. Everything is summed up into `norm`.
;;
;;}

(defn instantiate-def
  "Substitute in the `body` of a definition the parameters `params`
  by the actual arguments `args`."
  [params body args]
  (loop [args args, params params, sub {}]
    (if (seq args)
      (if (empty? params)
        (throw (ex-info "Not enough parameters (please report)" {:args args}))
        (recur (rest args) (rest params) (assoc sub (ffirst params) (first args))))
      (loop [params (reverse params), res body]
        (if (seq params)
          (recur (rest params) (list 'λ (first params) res))
          (stx/subst res sub))))))

(def +unfold-implict+ (atom nil))

(defn delta-reduction
  "Apply a strategy of delta-reduction in definitional environment `def-env`,
  context `ctx` and term `t`. If the flag `local?` is `true` then the definition
  is only looked for in `def-env`. By default it is also looked for in
  the current namespace (in Clojure only)."
  ([def-env ctx t] (delta-reduction def-env ctx t false))
  ([def-env ctx t local?]
   (if-not (stx/ref? t)
     (throw (ex-info "Cannot delta-reduce: not a reference term (please report)." {:term t}))
     (let [[name & args] t
           [status sdef] (defenv/fetch-definition def-env name local?)]
       (cond
         (= status :ko)
         (throw (ex-info "No such definition" {:term t :def-name name}))

         (implicit? sdef)
         (let [[status, implicit-term, _] (@+unfold-implict+ def-env ctx sdef args)]
           (if (= status :ko)
             (throw (ex-info "Cannot delta-reduce implicit term." implicit-term))
             [implicit-term true]))

         (> (count args) (:arity sdef))
         (throw (ex-info "Too many arguments to instantiate definition."
                  {:term t :def-name name
                   :nb-params (:arity sdef) :nb-args (count args)}))

         (definition? sdef)
         (if (:parsed-term sdef)
           (if (get (:opts sdef) :opaque)
             ;; the definition is opaque
             [t false]
             ;; the definition is transparent
             [(instantiate-def (:params sdef) (:parsed-term sdef) args) true])
           ;; no parsed term for definition
           (throw (ex-info "Cannot unfold term reference: no parsed term (please report)"
                    {:term t :def sdef})))

         (theorem? sdef)
         (if (:proof sdef)
           ;; unfolding works but yields very big terms
           ;; having a proof is like a certicate and thus
           ;; the theorem can now be considered as an abstraction, like
           ;; an axiom but with a proof...
           ;; [(instantiate-def (:params sdef) (:proof sdef) args) true]
           [t false]
           (throw (ex-info "Cannot use theorem with no proof."
                    {:term t :theorem sdef})))

         (axiom? sdef)
         [t false]

         ;; nothing known
         :else (throw (ex-info "Not a Latte definition (please report)."
                        {:term t :def sdef})))))))

(defn evaluation
  "Convert all λ/Π-terms' bodies into Clojure functions, and apply them when
  an application is seen.
  Variables within functions are marked as 'bound' and are translated
  into the name of the function argument, at call time."
 ([t] (evaluation defenv/empty-env {} [] t))
 ([def-env fn-env ctx t]
  (let [eva (partial evaluation def-env fn-env ctx)]
    (cond
      (stx/binder? t)
      (let [[binder [x type-x] body] t
            type-x' (eva type-x)]
        (list binder [x type-x']
              (fn [y] (evaluation def-env
                                  (assoc fn-env x y)
                                  (cons [y type-x'] ctx)
                                  body))))

      (stx/app? t)
      (let [[l r] (map eva t)]
        (if (stx/lambda? l)
          ((last l) r)
          [l r]))

      (stx/variable? t)
      (get fn-env t t)

      (stx/ascription? t)
      (cons (first t) (map eva (rest t)))

      (stx/ref? t)
      (let [[t' flag] (delta-reduction def-env ctx t)]
        (if flag
          (recur def-env fn-env ctx t')
          (cons (first t') (map eva (rest t')))))

      :else t))))

(defn quotation
  "Re-translate all remaining functions into standard λ/Π-terms by calling them.
  'taken' means free *and* bound variables and is used to prevent name clashes."
  [taken t]
  (let [quot (partial quotation taken)]
    (cond
      ;; A binder here means the function was not called during evaluation.
      ;; We call it now with the appropriate argument to extract the body.
      (stx/binder? t)
      (let [[binder [x type-x] f] t
            x' (stx/mk-fresh x taken)]
        (list binder [x' (quot type-x)]
          (quotation (conj taken x') (f x'))))

      (stx/app? t)
      (mapv quot t)

      (or (stx/ref? t) (stx/ascription? t))
      (cons (first t) (map quot (rest t)))

      :else t)))

(defn norm
  "Compose above functions to create the 'normalisation by evaluation' process."
 ([t] (norm defenv/empty-env [] t))
 ([def-env ctx t]
  (let [free (stx/free-vars t)]
    (quotation free (evaluation def-env {} ctx t)))))
