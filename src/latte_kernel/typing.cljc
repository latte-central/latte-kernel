(ns latte-kernel.typing
  (:require [latte-kernel.utils :as u]
            [latte-kernel.syntax :as stx]
            [latte-kernel.norm :as norm]
            [latte-kernel.defenv :as defenv]))
  
;;{
;; # Type checking
;;
;; Type checking, and more precisely **type inference**, is the *heart* of a
;; proof assistant based on type theory.
;;
;; In this namespace all the type-checking rules are implemented by dedicated
;; functions.
;;}

;;{
;; ## Type context
;;
;; We simply use a vector for the type context, which allows to
;; maintain the scoping rules at the price of some inefficiency
;; (fetching is O(n)). 
;;}

(defn ctx-fetch
  "Look for variable named `x` in the type context `ctx`.
  Returns the associated type or `nil` if there is no such variable."
  [ctx x]
  ;; (println "[ctx-fetch] ctx=" ctx "x=" x)
  (if (seq ctx)
    (if (= (first (first ctx)) x)
      (second (first ctx))
      (recur (rest ctx) x))
    nil))

(defn ctx-put
  "Add variable `x` bound to type `t` in context `ctx`, potentially
  shadowing other variables with the same name."
  [ctx x t]
  (cons [x t] ctx))

;;{
;; ## Synthesis rules
;;
;; All the type inference rules are given below.
;;
;;}

(declare type-of-type
         type-of-var
         type-of-prod
         type-of-abs
         type-of-app
         type-of-ref
         type-of-ascribe)

;;{
;; The following function is the main entry point for type inference.
;;}

(defn type-of-term
  "Infer the type of term `t` in definitional environment `def-env` 
  and type context `ctx`.
  The returned value is of the form `[:ok <type>]` if the inferred
  type is `<type>`, or `[:ko <info>]` in case of failure, with `<info>`
 an error map."
  [def-env ctx t]
  (let [[status ty]
        (cond
          (stx/kind? t) [:ko {:msg "Kind has not type" :term t}]
          (stx/type? t) (type-of-type)
          (stx/variable? t) (type-of-var def-env ctx t)
          ;; binders (lambda, prod)
          (stx/binder? t)
          (let [[binder [x ty] body] t]
            (case binder
              λ (type-of-abs def-env ctx x ty body)
              Π (type-of-prod def-env ctx x ty body)
              (throw (ex-info "No such binder (please report)" {:term t :binder binder}))))
          ;; references
          (stx/ref? t) (type-of-ref def-env ctx (first t) (rest t))
          ;; ascriptions
          (stx/ascription? t)
          (let [[_ e u] t]
            (type-of-ascribe def-env ctx e u))
          ;; applications
          (stx/app? t) (type-of-app def-env ctx (first t) (second t))
          :else
          (throw (ex-info "Invalid term (please report)" {:term t})))]
    ;;(println "--------------------")
    ;;(println "[type-of-term] t=" t)
    ;;(clojure.pprint/pprint ty)
    ;;(println "--------------------")
    [status ty]))

;;{
;; Type-checking is a derived form of type inference. Given a term `t`
;; and a type `T`, the first step is to infer the type of `t`, say `U`,
;; and then check that it is beta-equivalent to the expected type `T`.
;;}

(defn type-check?
  "Check if `term` has the given `type` in the definitional
  environment `def-env` and context `ctx`."
  [def-env ctx term type]
  ;;(println "[type-check?] term=" term "type=" type)
  ;;(println "    ctx=" ctx)
  (let [[status type'] (type-of-term def-env ctx term)]
    ;;(println "  ==> " status "type'=" type' "vs. type=" type)
    (if (= status :ok)
      (norm/beta-eq? def-env ctx type type')
      (throw (ex-info "Cannot check type of term" {:term term :from type'})))))

;;{
;;
;; ### The type of types
;;
;; The type of *the type of types* `✳` (or `:type`) is the kind `□` (or `:kind`).
;;
;; **Remark**: LaTTe uses an *impredicative* type theory, marked by the fact that
;; the kind `□` itself has no type.
;;  
;;     --------------------
;;     E |- Type ::> Kind
;;
;;}

(defn type-of-type
  "Return type type of `:type`."
  []
  [:ok '□])

;;{
;;
;;  ### The type of variables
;;
;;  The type of a variable is to be found in the context.
;;  And it must be associated to a type or a kind.
;;
;;
;;        ty::>Type or t::>Kind in E
;;     ------------------------------
;;        E,x::ty |- x ::> ty
;;}

(defn type-of-var
  "Infer the type of variable `x` in context `ctx`."
  [def-env ctx x]
  (if-let [ty (ctx-fetch ctx x)]
    (let [[status sort] (let [ty' (norm/normalize def-env ctx ty)]
                          (if (stx/kind? ty')
                            [:ok ty']
                            (type-of-term def-env ctx ty)))]
      (if (= status :ko)
        [:ko {:msg "Cannot calculate type of variable." :term x :from sort}]
        (if (stx/sort? sort)
          [:ok ty]
          [:ko {:msg "Not a correct type (super-type is not a sort)" :term x :type ty :sort sort}])))
    [:ko {:msg "No such variable in type context" :term x}]))


;;{
;;
;; ### The type of products
;;
;;  The type of a product is a *sort*, either the type of types or the
;; type of kinds.
;;
;;    E |- A ::> s1     E,x:A |- B ::> s2
;;    -----------------------------------
;;     E |- prod x:A . B  ::>  s2
;;}

(defn type-of-prod
  "Infer the type of a product with bound variable `x` of
  type `A` in body `B`."
  [def-env ctx x A B]
  (let [[status sort1] (type-of-term def-env ctx A)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate domain type of product." :term A :from sort1}]
      (let [sort1' (norm/normalize def-env ctx sort1)]
        (if (not (stx/sort? sort1'))
          [:ko {:msg "Not a valid domain type in product (super-type not a sort)" :term A :type sort1}]
          (let [ctx' (ctx-put ctx x A)
                [status sort2] (type-of-term def-env ctx' B)]
            (if (= status :ko)
              [:ko {:msg "Cannot calculate codomain type of product." :term B :from sort2}]
              (let [sort2' (norm/normalize def-env ctx sort2)]
                ;; (println "sort2' = " sort2' " sort? " (stx/sort? sort2'))
                (if (not (stx/sort? sort2'))
                  [:ko {:msg "Not a valid codomain type in product (not a sort)" :term B :type sort2}]
                  [:ok sort2])))))))))


;;{
;;
;; ### The type of abstractions
;;
;; The type of an abstraction is simply the coresponding
;; product, on of the beauties of type theory.
;;
;;
;;    E,x:A |- t ::> B  E |- prod x:A. B ::> s
;;    --------------------------------------------
;;    E |- lambda x:A . t  ::>  prod x:A . B
;;}

(comment

(defn type-of-abs [def-env ctx x A t]
  (let [ctx' (ctx-put ctx x A)
        [status B] (type-of-term def-env ctx' t)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate codomain type of abstraction."
            :term (list 'λ [x A] t) :from B}]
      (let [tprod (list 'Π [x A] B)
            [status sort] (type-of-term def-env ctx tprod)]
        (if (= status :ko)
          [:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type)."
                :term (list 'λ [x A] t)
                :codomain B :from sort}]
          (if (not (stx/sort? (norm/normalize def-env ctx sort)))
            [:ko {:msg "Not a valid codomain type in abstraction (super-type not a sort)."
                  :term (list 'λ [x A] t)
                  :codomain B
                  :type sort}]
            [:ok tprod]))))))

(example
 (type-of-term {} '[[bool ✳] [t bool] [y bool]]
          '(λ [x bool] x))
 => '[:ok (Π [x bool] bool)])

(example
 (type-of-term {} [] '(λ [x ✳] x)) => '[:ok (Π [x ✳] ✳)])

(example
 (type-of-term {} '[[y bool]] '(λ [x bool] x))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x bool] x),
           :from {:msg "Cannot calculate type of variable.", :term x,
                  :from {:msg "No such variable in type context", :term bool}}}])

(example
 (type-of-term {} '[[y ✳] [z y]] '(λ [x z] x))

 
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x z] x),
           :from {:msg "Not a correct type (super-type is not a sort)", :term x, :type z, :sort y}}])

(example
 (type-of-term {} '[[y bool]] '(λ [x ✳] y))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] y),
           :from {:msg "Cannot calculate type of variable.", :term y,
                  :from {:msg "No such variable in type context", :term bool}}}])

(example
 (type-of-term {} '[[y bool]] '(λ [x ✳] □))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] □),
           :from {:msg "Kind has not type" :term □}}])

(example
 (type-of-term {} '[[y bool]] '(λ [x ✳] ✳))
 => '[:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type).",
           :term (λ [x ✳] ✳), :codomain □,
           :from {:msg "Cannot calculate codomain type of product.", :term □,
                  :from {:msg "Kind has not type", :term □}}}])
(example
 (type-of-term {} '[[w ✳] [y w] [z y]] '(λ [x ✳] z))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] z),
           :from {:msg "Not a correct type (super-type is not a sort)", :term z, :type y, :sort w}}])

;;{
;;       E |- rator ::> prod x:A . B    E|- rand :: A
;;    -------------------------------------------------
;;          E |- rator rand : B [rand/x]
;;}

(defn type-of-app [def-env ctx rator rand]
  (let [[status trator] (type-of-term def-env ctx rator)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate operator (left-hand) type in application."
            :term [rator rand] :from trator}]
      (let [trator' (norm/normalize def-env ctx trator)]
        (if (not (stx/prod? trator'))
          [:ko {:msg "Not a product type for operator (left-hand) in application." :term [rator rand] :operator-type trator}]
          (let [[_ [x A] B] trator']
            ;; (println "[type-of-app] trator'=" trator')
            (if (not (type-check? def-env ctx rand A))
              [:ko {:msg "Cannot apply: type domain mismatch" :term [rator rand] :domain A :operand rand}]
              (do ;;(println "[type-of-app] subst...")
                  ;;(println "    B = " B)
                  ;;(println "    x = " x)
                  ;;(println "    rand = " rand)
                  (let [res (stx/subst B x rand)]
                    ;;(println "   ===> " res)
                    [:ok res])))))))))


(example
 (type-of-term {} '[[bool ✳] [y bool]]
          '[(λ [x bool] x) y])
 => '[:ok bool])


;;{
;;    D |- ref :: [x1 t1] [x2 t2] ... [xN tN] -> t
;;    E |- e1 :: t1   E, x1:t1 |- e2 :: t2
;;    ...
;;    E, x1:t1, ..., xM-1:tM-1 |- eM :: tM
;; -------------------------------------------------------------------------------------
;;      D, E |- (ref e1 e2 ... eM)
;;              ::> (prod [xM+1 tM+1] ... (prod [xN tN] t [e1/x1, e2/x2, ...eM/xM]) ...)
;;}

(defn type-of-ref [def-env ctx name args]
  (let [[status ty]
        (let [[status ddef] (defenv/fetch-definition def-env name)]
          (cond
            (= status :ko) [:ko ddef]
            (not (defenv/latte-definition? ddef))
            (throw (ex-info "Not a LaTTe definition (please report)." {:def ddef}))
            (defenv/special? ddef)
            (throw (ex-info "Special should not occur at typing time (please report)"
                            {:special ddef :term (list* name args)}))
            (defenv/notation? ddef)
            (throw (ex-info "Notation should not occur at typing time (please report)"
                            {:notation ddef :term (list* name args)}))
            (and (defenv/theorem? ddef)
                 (= (:proof ddef) false))
            [:ko {:msg "Theorem has no proof." :thm-name (:name ddef)}]
            (> (count args) (:arity ddef))
            [:ko {:msg "Too many arguments for definition." :term (list* name args) :arity (:arity ddef)}]
            :else
            (loop [args args, params (:params ddef), sub {}]
              ;; (println "args=" args "params=" params "sub=" sub)
              (if (seq args)
                (let [arg (first args)
                      ty (stx/subst (second (first params)) sub)]
                  ;; (println "arg=" arg "ty=" ty)
                  (if (not (type-check? def-env ctx arg ty))
                    [:ko {:msg "Wrong argument type"
                          :term (list* name args)
                          :arg arg
                          :expected-type ty}]
                    (recur (rest args) (rest params) (assoc sub (ffirst params) arg))))
                ;; all args have been checked
                (loop [params (reverse params), res (:type ddef)]
                  (if (seq params)
                    (recur (rest params) (list 'Π (first params) res))
                    ;; all params have been handled
                    (do
                      ;;(println "[type-of-ref] res = " res " sub = " sub)
                      [:ok (stx/subst res sub)])))))))]
    ;;(println "---------------------")
    ;;(println "[type-of-ref] name=" name "args=" args)
    ;;(clojure.pprint/pprint ty)
    ;;(println "---------------------")
    [status ty]))

(example
 (type-of-term {'test (defenv/map->Definition
                        '{:params [[x ✳] [y ✳]]
                          :type ✳
                          :arity 2})}
          '[[a ✳] [b ✳]]
          '(test a b))
 => '[:ok ✳])

(example
 (type-of-term {'test (defenv/map->Definition
                        '{:params [[x ✳] [y ✳]]
                          :type ✳
                          :arity 2})}
          '[[bool ✳] [a ✳] [b bool]]
          '(test a b))
 => '[:ko {:msg "Wrong argument type", :term (test b), :arg b, :expected-type ✳}])

(defn type-of
  ([t] (type-of {} [] t))
  ([ctx t] (type-of {} ctx t))
  ([def-env ctx t]
   (let [[status ty] (type-of-term def-env ctx t)]
     (if (= status :ko)
       (throw (ex-info "Type checking error" ty))
       ty))))

(defn proper-type?
  ([t] (proper-type? {} [] t))
  ([ctx t] (proper-type? {} ctx t))
  ([def-env ctx t]
   (let [ty (type-of def-env ctx t)]
     (let [sort (norm/normalize def-env ctx ty)]
       (stx/sort? sort)))))

)
