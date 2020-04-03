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
 1. translating λ-terms into a nbe-specific syntax, in which
   λ-exprs are replaced by Clojure functions.
 2. normalising those terms, aka applying the functions wherever possible.
 3. retranslating back into normal λ-terms.

Those three steps are represented here with the functions
 `evaluation`, `normalisation`, and `quotation`, all summed up into `norm`.

 It is important to note that `evaluation` works recursively, depth-first.

 The major trick used here is the following: <br>
 In this valid lambda expression `(λ [a ✳] [(λ [b ✳] [a b]) c])`
 which would be normalised into `(λ [a ✳] [a c])`,
 we can't directly tell Clojure to call `(fn [b] [a b])` on argument `c`,
 since `a` isn't defined in this context.
 We therefore can't make the normalisation part recursively & depth-first too. <br>
 The trick is using the power of the Lisp quote to delay the call to
 the inner normalisation, by creating (in `evaluation`) a quoted function that
 will, only when called, call `normalisation` on its previously-evaluated body. <br>
 This makes it so that `eval`-ing the outer function actually processes
 the normalisation of its body, which means applying the inner function.

 Because of this, the functions `evaluation` and `normalisation` need to be
 defined in reverse order, since the former uses the latter.

TODO: finish doc, talk about bound and unbound variables, and metadata



```clojure
(defn normalisation
  "Actually apply normalisation, staying in nbe-specific syntax."
  [t]
  (if (or (stx/variable? t) (stx/host-constant? t) (keyword? t))
    t
    (case (first t)
      ::lambda (let [var-name (-> t meta ::var-name)
                     var-type (-> t meta ::var-type normalisation)]
                 (with-meta [::lambda (eval (second t))]
                   {::var-name var-name ::var-type var-type}))
      ::pi (let [var-name (-> t meta ::var-name)
                 var-type (-> t meta ::var-type normalisation)]
             (with-meta [::pi (normalisation (second t))]
               {::var-type var-type, ::var-name var-name}))
      ::app (let [[_ l r] t
                  l' (normalisation l)
                  r' (normalisation r)]
              (if (and (vector? l') (= ::lambda (first l')))
                ;; We can apply the function contained in l'
                ((second l') r')
                [::app l' r']))
      ::ref (vector* ::ref (second t) (map normalisation (drop 2 t)))
      ::asc (vector* ::asc (map normalisation (rest t))))))

(defn evaluation
  "Convert from LaTTe internal syntax to nbe-specific syntax, recursively.
  All simple terms are keywordized, and composite terms are translated into
  a pair with a special keyword, excepts lambdas which are turned into real
  Clojure functions.
  Variables which were seen on the way down are marked as 'bound' and are not
  translated at all to allow calling directly the functions."
 ([t] (evaluation t #{}))
 ([t bound]
  {:pre [(stx/term? t)]}
  (letfn [(eva [te] (evaluation te bound))]
    (cond
      ;; previously bound variable
      (and (stx/variable? t) (contains? bound t))
      t

      ;; 'sort' or normal variable
      (or (stx/sort? t) (stx/variable? t))
      (keyword "latte-kernel.nbe" (name t))

      ;; lambda
      (stx/lambda? t)
      (let [[_ [x tx] body] t
            body' (evaluation body (conj bound x))]
        ;; We create a quoted function and attach as metadata the name originally
        ;; used as argument, and its type. Useful later for quotation.
        ;; We also add a delayed call to normalisation to be able to reduce
        ;; nested expressions
        (with-meta [::lambda `(fn [~x] (normalisation ~body'))]
          {::var-name (eva x)
           ::var-type (eva tx)}))

      ;; pi
      (stx/prod? t)
      (let [[_ [x tx] body] t]
        (with-meta [::pi (eva body)]
          {::var-name (eva x)
           ::var-type (eva tx)}))

      ;; reference
      (stx/ref? t)
      (vector* ::ref (first t) (map eva (rest t)))

      ;; application
      (stx/app? t)
      (vector* ::app (map eva t))

      ;; ascription
      (stx/ascription? t)
      (vector* ::asc (map eva (rest t)))

      ;; host constants
      (stx/host-constant? t) ;t
      (throw (ex-info "Don't know what to do with host-constant" {:host-constant t}))))))

(defn quotation
  "From nbe-specific syntax to normal LaTTe internal syntax."
  [t]
  {:post [(stx/term? %)]}
  (cond
    (stx/variable? t)  t
    (keyword? t) (symbol (name t))
    :default
    (case (first t)
      ::lambda (let [f (second t)
                     var-name (-> t meta ::var-name quotation)
                     var-type (-> t meta ::var-type quotation)]
                 ;; TODO: update comment
                 ;; f has never been called, so the body wasn't reduced.
                 ;; We call it with the associated variable to unfold everything
                 (list 'λ [var-name var-type] (quotation (f var-name))))
      ::pi (let [body (second t)
                 var-name (-> t meta ::var-name name symbol)
                 var-type (-> t meta ::var-type quotation)]
             (list 'Π [var-name var-type] (quotation body)))
      ::app (vec (map quotation (rest t)))
      ::ref (cons (second t) (map quotation (rest (rest t))))
      ::asc (cons ::stx/ascribe (map quotation (rest t))))))

(defn norm
  "Compose above functions to create the 'normalisation by evaluation' process."
  [t]
  {:pre [(stx/term? t)]
   :post [(stx/term? %), (nil? (meta %))]}
  ((comp quotation normalisation evaluation) t))
```
