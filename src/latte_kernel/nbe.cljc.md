```clojure
(ns latte-kernel.nbe
  (:require [latte-kernel.utils :refer [vector*]]
            [latte-kernel.syntax :as stx]))

```

 # Normalisation by evaluation

 Instead of applying ourselves the normalisation as seen in `norm.cljc`,
 we want to let the Clojure language do for us the complicated part:
 substituting argument names for their value while respecting nested scopes,
 aka calling the λ-functions.

 This is done in three steps:
 1. translating terms into a nbe-specific syntax, in which
    λ-expressions are replaced by Clojure functions.
 2. normalising those terms, aka applying the functions wherever possible.
 3. retranslating back into normal λ-terms.

Those three steps are represented here with the functions
 `evaluation`, `normalisation`, and `quotation`, all summed up into `norm`.



```clojure
(defn evaluation
  "Convert from LaTTe internal syntax to nbe-specific syntax, recursively.
  All simple terms are left as-is, composite terms are translated into
  a pair with a special keyword, excepts binders which are turned into real
  Clojure functions.
  Variables within functions are marked as 'bound' and are translated
  into the name of the function argument, at call time."
 ([t] (evaluation [() #{}] t))
 ([[env bound] t]
  {:pre [(stx/term? t)]}
  (letfn [(eva [te] (evaluation [env bound] te))
          (env-push [x y] [(cons [x y] env) (conj bound x)])
          (env-fetch [x] (some #(when (= x (first %)) (second %)) env))]
    (cond
      ;; bound variable
      (and (stx/variable? t) (contains? bound t))
      (env-fetch t)

      ;; binder
      (stx/binder? t)
      (let [[binder [x tx] body] t]
        [::binder binder x (eva tx) (fn [y] (evaluation (env-push x y) body))])

      ;; reference
      (stx/ref? t)
      (vector* ::ref (first t) (map eva (rest t)))

      ;; application
      (stx/app? t)
      (vector* ::app (map eva t))

      ;; ascription
      (stx/ascription? t)
      (vector* ::asc (map eva (rest t)))

      ;; other cases (including unbound variables and sorts)
      :else t))))

(defn normalisation
  "Actually apply normalisation, staying in nbe-specific syntax."
  [t]
  (if (stx/term? t) ;; other cases above
    t
    (case (first t)
      ::binder (let [[_ binder x type-x f] t]
                 [::binder binder x (normalisation type-x) f])
      ::app (let [[_ l r] t
                  l' (normalisation l)
                  r' (normalisation r)]
              (if (and (vector? l') (= ::binder (first l')))
                ;; We can apply the function contained in l'
                (recur ((last l') r'))
                [::app l' r']))
      ::ref (vector* ::ref (second t) (map normalisation (drop 2 t)))
      ::asc (vector* ::asc (map normalisation (rest t))))))

(defn quotation
  "From nbe-specific syntax to normal LaTTe internal syntax.
  'taken' means free *and* bound variables, and is used to prevent name clashes."
  [taken t]
  {:post [(stx/term? %)]}
  (if (stx/term? t)
    t
    (let [quot (partial quotation taken)]
      (case (first t)
        ;; A binder here means it was not called during normalisation, so its
        ;; body may not be normalised. We call it now with the appropriate
        ;; argument, and normalise the result.
        ::binder (let [[_ binder x type-x f] t
                       x' (stx/mk-fresh x taken)]
                   (list binder [x' (quot type-x)]
                     (quotation (conj taken x') (normalisation (f x')))))
        ::app (vec (map quot (rest t)))
        ::ref (cons (second t) (map quot (rest (rest t))))
        ::asc (cons ::stx/ascribe (map quot (rest t)))))))

(defn norm
  "Compose above functions to create the 'normalisation by evaluation' process."
  [t]
  {:pre [(stx/term? t)]
   :post [(stx/term? %)]}
  (let [free (stx/free-vars t)]
    (->> t evaluation normalisation (quotation free))))
```
