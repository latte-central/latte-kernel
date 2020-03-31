(ns latte-kernel.nbe
  (:require [latte-kernel.syntax :as stx]))

(defn evaluation
  "Convert from LaTTe internal syntax to nbe-specific syntax, recursively.
  All terms are just translated into pair with a special keyword,
  excepts lambdas which are turned into real Clojure functions, quoted to avoid
  calling nested function in bottom-up manner."
 ([t] (evaluation t #{}))
 ([t bound]
  {:pre [(stx/term? t)]}
  (cond
    ;; sort
    (stx/sort? t)
    [::sort (keyword "latte-kernel.nbe" (str t))]

    ;; previously bound variable
    (and (stx/variable? t) (contains? bound t))
    t

    ;; normal variable
    (stx/variable? t)
    [::var (keyword "latte-kernel.nbe" (str t))]

    ;; lambda
    (stx/lambda? t)
    (let [[_ [x tx] body] t
          body2 (evaluation body (conj bound x))]
      [::lambda
       (with-meta (list 'fn [x] body2)
         {::var-name (keyword "latte-kernel.nbe" (str x))
          ::var-type (evaluation tx bound)})])

    ;; pi
    (stx/prod? t)
    (let [[_ [x tx] body] t]
      [::pi
       (with-meta (evaluation body (conj bound x))
         {::var-name (keyword "latte-kernel.nbe" (str x))
          ::var-type (evaluation tx bound)})])

    ;; reference
    (stx/ref? t)
    (let [[ref-name & args] t
          args' (map #(evaluation % bound) args)]
      (vec (cons ::ref (cons ref-name args'))))

    ;; application
    (stx/app? t)
    (let [u (evaluation (first t) bound)
          u' (evaluation (second t) bound)]
      [::app u u'])

    ;; ascription
    (stx/ascription? t)
    [::asc (evaluation (second t) bound) (evaluation (last t) bound)]

    ;; host constants
    (stx/host-constant? t)
    t)))

(defn normalisation
  "Actually apply normalisation, staying in nbe-specific syntax."
  [t]
  (if (or (stx/variable? t) (stx/host-constant? t))
    t
    (case (first t)
      ::sort t
      ::var t
      ::lambda (let [f (second t)
                     var-type (normalisation (::var-type (meta f)))]
                 [::lambda (vary-meta f assoc ::var-type var-type)])
      ::pi (let [body (second t)
                 var-name (::var-name (meta body))
                 var-type (normalisation (::var-type (meta body)))]
             [::pi (with-meta (normalisation body)
                     {::var-type var-type, ::var-name var-name})])
      ::app (let [[_ l r] t
                  l' (normalisation l)
                  r' (normalisation r)]
              (if (and (vector? l') (= ::lambda (first l')))
                ;; We can apply the function contained in l'
                ((eval (second l')) r')
                [::app l' r']))
      ::ref (vec (cons (second t) (nth t 2)))
      ::asc [::asc (normalisation (second t)) (normalisation (last t))])))

(defn quotation
  "From nbe-specific syntax to normal LaTTe internal syntax."
  [t]
  {:post [(stx/term? %)]}
  (if (or (stx/variable? t) (stx/host-constant? t))
    t
    (case (first t)
      (::sort ::var) (symbol (name (second t)))
      ::lambda (let [f (second t)
                     var-name (-> f meta ::var-name name symbol)
                     var-type (-> f meta ::var-type quotation)]
                 ;; f has never been called, so the body wasn't reduced.
                 ;; We call it with the associated variable to unfold everything
                 (list 'λ [var-name var-type] (quotation (normalisation ((eval f) var-name)))))
      ::pi (let [body (second t)
                 var-name (-> body meta ::var-name name symbol)
                 var-type (-> body meta ::var-type quotation)]
             (list 'Π [var-name var-type] (quotation body)))
      ::app [(quotation (second t)) (quotation (last t))]
      ::ref (vec (cons (second t) (nth t 2)))
      ::asc (list ::stx/ascribe (quotation (second t)) (quotation (last t))))))

(defn norm
  "Compose above functions to create the 'normalisation by evaluation' process."
  [t]
  {:pre [(stx/term? t)]
   :post [(stx/term? %), (nil? (meta %))]}
  ((comp quotation normalisation evaluation) t))
