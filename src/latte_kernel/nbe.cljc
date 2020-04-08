(ns latte-kernel.nbe
  (:require [latte-kernel.syntax :as stx]))

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

(defn evaluation
  "Convert all λ/Π-terms' bodies into Clojure function, and apply when
  an application is seen.
  Variables within functions are marked as 'bound' and are translated
  into the name of the function argument, at call time."
 ([t] (evaluation {} t))
 ([subst t]
  (let [eva (partial evaluation subst)]
    (cond
      (stx/binder? t)
      (let [[binder [x type-x] body] t]
        (list binder [x (eva type-x)]
              (fn [y] (evaluation (assoc subst x y) body))))

      (stx/app? t)
      (let [[l r] (map eva t)]
        (if (stx/binder? l)
          ((last l) r)
          [l r]))

      (stx/variable? t)
      (get subst t t)

      (or (stx/ref? t) (stx/ascription? t))
      (cons (first t) (map eva (rest t)))

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
  [t]
  #_{:pre [(stx/term? t)] :post [(stx/term? %)]}
  (let [free (stx/free-vars t)]
    (quotation free (evaluation t))))
