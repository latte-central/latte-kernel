(ns latte-kernel.typing
  (:require [latte-kernel.syntax :as stx]
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

(declare unfold-implicit)

(defn type-of-term
  "Infer the type of term `t` in definitional environment `def-env`
  and type context `ctx`.
  The returned value is of the form `[:ok <type> t']` if the inferred
  type is `<type>`, or `[:ko <info> nil]` in case of failure, with `<info>`
  an error map.  The term `t'` returned is the rewrite of the term so
  that implicits can be erased."
  [def-env ctx t]
  (let [[status ty t']
        (cond
          (stx/kind? t) [:ko {:msg "Kind has not type" :term t} nil]
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
          ;; host constants
          (stx/host-constant? t) (throw (ex-info "Host constant should not be remaining while typing (please report)"
                                                 {:term t}))
          ;; applications
          (stx/app? t) (type-of-app def-env ctx (first t) (second t))
          :else
          (throw (ex-info "Invalid term (please report)" {:term t})))]
    ;;(println "--------------------")
    ;;(println "[type-of-term] t=" t)
    ;;(clojure.pprint/pprint ty)
    ;;(println "--------------------")
    [status ty t']))

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
  (let [[status type' _] (type-of-term def-env ctx term)]
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
  [:ok '□ '✳])

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
    (let [[status sort ty']
          (let [ty' (norm/normalize def-env ctx ty)]
            (if (stx/kind? ty')
              [:ok ty' ty]
              (type-of-term def-env ctx ty)))]
      (if (= status :ko)
        [:ko {:msg "Cannot calculate type of variable." :term x :from sort} nil]
        (if (stx/sort? sort)
          [:ok ty' x]
          [:ko {:msg "Not a correct type (super-type is not a sort)" :term x :type ty' :sort sort} nil])))
    ;; not found
    [:ko {:msg "No such variable in type context" :term x} nil]))


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
  "Infer the type of a product with bound variable `x` of type `A` in body `B`."
  [def-env ctx x A B]
  (let [[status sort1 A'] (type-of-term def-env ctx A)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate domain type of product." :term A :from sort1} nil]
      (let [sort1' (norm/normalize def-env ctx sort1)]
        (if (not (stx/sort? sort1'))
          [:ko {:msg "Not a valid domain type in product (super-type not a sort)" :term A :type sort1}]
          (let [ctx' (ctx-put ctx x A) ;; or unfolded ? (ctx-put ctx x A')
                [status sort2 B'] (type-of-term def-env ctx' B)]
            (if (= status :ko)
              [:ko {:msg "Cannot calculate codomain type of product." :term B :from sort2} nil]
              (let [sort2' (norm/normalize def-env ctx sort2)]
                ;; (println "sort2' = " sort2' " sort? " (stx/sort? sort2'))
                (if (not (stx/sort? sort2'))
                  [:ko {:msg "Not a valid codomain type in product (not a sort)" :term B :type sort2} nil]
                  [:ok sort2 (list 'Π [x A'] B')])))))))))


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


(defn type-of-abs
  "Infer the type of an  with bound variable `x` of
  type `A` in body `B`."
  [def-env ctx x A t]
  (let [[status err A'] (type-of-term def-env ctx A)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate domain type of abstraction."
            :term (list 'λ [x A] t) :from err} nil]
      (let [ctx' (ctx-put ctx x A) ;; or A' ? (ctx-put ctx x A')
            [status B t'] (type-of-term def-env ctx' t)]
        (if (= status :ko)
          [:ko {:msg "Cannot calculate codomain type of abstraction."
                :term (list 'λ [x A] t) :from B} nil]
          (let [tprod (list 'Π [x A] B) ;; or A' ? (list 'Π [x A'] B)
                [status sort tprod'] (type-of-term def-env ctx tprod)]
            (if (= status :ko)
              [:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type)."
                    :term (list 'λ [x A] t')
                    :codomain B :from sort} nil]
              (if (not (stx/sort? (norm/normalize def-env ctx sort)))
                [:ko {:msg "Not a valid codomain type in abstraction (super-type not a sort)."
                      :term (list 'λ [x A] t')
                      :codomain B
                      :type sort}]
                [:ok tprod (list 'λ [x A'] t')]))))))))


;;{
;;
;; ### The type of applications
;;
;; The typing of an application is a little bit more demanding,
;; especially because it involves the substitution of the
;; bound variable by the operand in the return type.
;;
;;
;;       E |- rator ::> prod x:A . B    E|- rand :: A
;;    -------------------------------------------------
;;          E |- rator rand : B [rand/x]
;;}

(defn type-of-app
  "Infer the type of an application with operator `rator` and operand `rand`."
  [def-env ctx rator rand]
  (let [[status trator rator'] (type-of-term def-env ctx rator)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate operator (left-hand) type in application."
            :term [rator rand] :from trator} nil]
      (let [[status trand rand'] (type-of-term def-env ctx rand)]
        (if (= status :ko)
          [:ko {:msg "Cannot calculate operand (right-hand) type in application."
                :term [rator rand] :from trand} nil]
          (let [trator' (norm/normalize def-env ctx trator)]
            (if (not (stx/prod? trator'))
              [:ko {:msg "Not a product type for operator (left-hand) in application." :term [rator rand] :operator-type trator}]
              (let [[_ [x A] B] trator']
                ;; (println "[type-of-app] trator'=" trator')
                (if (not (type-check? def-env ctx rand A)) ;; or rand' ? (not (type-check? def-env ctx rand' A))
                  [:ko {:msg "Cannot apply: type domain mismatch" :term [rator rand] :domain A :operand rand}]
                  (do ;;(println "[type-of-app] subst...")
                    ;;(println "    B = " B)
                    ;;(println "    x = " x)
                    ;;(println "    rand = " rand)
                    (let [res (stx/subst B x rand)] ;; or rand' ? (stx/subst B x rand')
                      ;;(println "   ===> " res)
                      [:ok res [rator' rand']])))))))))))

;;{
;;
;; ### The type of references
;;
;; A reference to a defined term in LaTTe is like a 'function call' in a
;; programming language. As such, in order to type a reference
;; one has to unfold the reference by the defined term.
;; The type is then inferred from the unfolded term.
;;
;;
;;    D |- ref :: [x1 t1] [x2 t2] ... [xN tN] -> t
;;    E |- e1 :: t1   E, x1:t1 |- e2 :: t2
;;    ...
;;    E, x1:t1, ..., xM-1:tM-1 |- eM :: tM
;; -------------------------------------------------------------------------------------
;;      D, E |- (ref e1 e2 ... eM)
;;              ::> (prod [xM+1 tM+1] ... (prod [xN tN] t [e1/x1, e2/x2, ...eM/xM]) ...)
;;
;;}

;;{
;; A reference is of the form `(ref e1 e2 ... eM)` where `ref` is a name and the `ei`'s are arbitrary expressions.
;; It can be a reference to either:
;;  - a defined term such as a parametric definition or an axiom
;;  - a theorem, which is a particular case of a defined term
;;  - an implicit
;;
;; Both the two first cases are handled by the function `type-of-refdef` below. The only difference
;; is that a theorem is a defined term only if it has been demonstrated. Put in other terms, it
;; is forbidden to reference a theorem with no-proof. The third case allows to perform arbibrary
;; computations during the type synthesis phase, it is handled by the `type-of-implicit` function.
;;}

(declare type-of-refdef)
(declare type-of-implicit)

(defn type-of-ref [def-env ctx name args]
  (let [[status ty nref]
        (let [[status ddef] (defenv/fetch-definition def-env name)]
          (cond
            (= status :ko) [:ko ddef]
            (not (defenv/latte-definition? ddef))
            (throw (ex-info "Not a LaTTe definition (please report)." {:def ddef}))
            (defenv/notation? ddef)
            (throw (ex-info "Notation should not occur at typing time (please report)"
                            {:notation ddef :term (list* name args)}))
            (and (defenv/theorem? ddef)
                 (not (:proof ddef)))
            [:ko {:msg "Theorem has no proof." :thm-name (:name ddef)} nil]
            (defenv/implicit? ddef)
            (type-of-implicit def-env ctx ddef args)
            (and (not (defenv/definition? ddef))
                 (not (defenv/theorem? ddef))
                 (not (defenv/axiom? ddef)))
            (throw (ex-info "Unsupported definitional entity, expecting a true definition or a theorem name"
                            {:name name, :entity ddef}))
            (> (count args) (:arity ddef))
            [:ko {:msg "Too many arguments for definition." :term (list* name args) :arity (:arity ddef)}]
            :else
            (type-of-refdef def-env ctx name ddef args)))]
    ;;(println "---------------------")
    ;;(println "[type-of-ref] name=" name "args=" args)
    ;;(clojure.pprint/pprint ty)
    ;;(println "---------------------")
    [status ty nref]))

;;{
;; #### Typing defined terms
;;
;; The standard processing of a reference is to construct the lambda-term corresponding
;; to the unfolding of a defined term. This is by substituting the parameters of the
;; defined term by the arguments of the reference. LaTTe allows the partial unfolding
;; of the defined terms, thus at the end we generalise for the remaining
;; uninstantiated parameters (as lambda-abstractions).
;;}

(declare type-of-args)
(declare prepare-argument-subst)
(declare generalize-params)

(defn type-of-refdef [def-env ctx name ddef args]
  (let [[status, targs, args'] (type-of-args def-env ctx args)]
    (if (= status :ko)
      [:ko targs nil]
      (let [[status, res]
            ;; (prepare-argument-subst def-env ctx name args' targs (:params ddef))
            ;; maybe do not replace by the unfolded terms
            (prepare-argument-subst def-env ctx name args targs (:params ddef))]
        (if (= status :ko)
          [:ko res]
          (let [[params sub] res
                expanded-term (stx/subst (:type ddef) sub)
                typ (generalize-params (reverse params) expanded-term)]
            ;; (let [[status err typ'] (type-of-term def-env ctx typ)]
            ;;   (if (= status :ko)
            ;;     [:ko err nil]
            ;;     [:ok typ' (list* name args')]))
            ;; [:ok typ (list* name args')] ;;  no unfold (???)
            [:ok typ (list* name args)]))))))



(defn type-of-args
  "Compute the type of an argument list."
  [def-env ctx args]
  (loop [args args, targs [], args' []]
    (if (seq args)
      (let [[status typ arg'] (type-of-term def-env ctx (first args))]
        (if (= status :ko)
          [:ko typ nil]
          (recur (rest args) (conj targs [(first args) typ]) (conj args' arg'))))
      [:ok targs args'])))

;;{
;; The function below realizes the substitution of the parameters by
;; their corresponding argument. The substitution `sub` is represented
;; as a map.
;;}

(defn prepare-argument-subst [def-env ctx name args targs params]
  (loop [args args, targs targs, params params, sub {}]
    ;; (println "args=" args "params=" params "sub=" sub)
    (if (seq args)
      (let [arg (first args)
            targ (second (first targs))
            ty (stx/subst (second (first params)) sub)]
        ;; (println "arg=" arg "ty=" ty)
        (if (not (type-check? def-env ctx arg ty))
          [:ko {:msg "Wrong argument type"
                :term (list* name args)
                :arg arg
                :arg-type targ
                :expected-type ty}]
          (recur (rest args) (rest targs) (rest params) (assoc sub (ffirst params) arg))))
      ;; all args have been checked
      [:ok [params sub]])))

;;{
;; The following function generalizes the remaining uninstantiated parameters.
;;}

(defn generalize-params [params res-type]
  (loop [params params, res res-type]
    (if (seq params)
      (recur (rest params) (list 'Π (first params) res))
      res)))

(defn type-of-implicit-args
  "Compute the type of an argument list, for an implicit.
  If the argument is not a term, then it is kept in the resulting
  argument list."
  [def-env ctx args]
  (loop [args args, targs [], args' []]
    (if (seq args)
      (if (not (stx/host-constant? (first args)))
        (let [[status typ arg'] (type-of-term def-env ctx (first args))]
          (if (= status :ko)
            [:ko typ nil]
            (recur (rest args) (conj targs [(first args) typ]) (conj args' arg'))))
        ;; a host-constant that we  pass "as it is" to the implicit function
        (recur (rest args) (conj targs (second (first args))) (conj args' (second (first args)))))
      [:ok targs args'])))

(defn unfold-implicit [def-env ctx implicit-def args]
  (let [[status, targs, args'] (type-of-implicit-args def-env ctx args)]
    (if (= status :ko)
      [:ko targs]
      (try [:ok, (apply (:implicit-fn implicit-def) def-env ctx targs), args']
           (catch Exception exc
             [:ko (merge {:implicit (:name implicit-def)
                          :msg (.getMessage exc)}
                         (ex-data exc)) nil])))))

;; circular dependency hack
(norm/install-unfold-implicit! unfold-implicit)

(defn type-of-implicit [def-env ctx implicit-def args]
  (let [[status, implicit-term, args'] (unfold-implicit def-env ctx implicit-def args)]
    ;; (println "implicit-term=" implicit-term)
    (if (= status :ko)
      [:ko implicit-term nil]
      ;; recursive typing of implicit-generated term
      (type-of-term def-env ctx implicit-term))))

(defn rebuild-type [def-env ctx ty]
  (let [vfresh (gensym "fresh")
        [status ty' _] (type-of-term def-env (cons [vfresh ty] ctx) vfresh)]
    [status ty']))

(defn type-of
  ([t] (type-of defenv/empty-env [] t))
  ([ctx t] (type-of defenv/empty-env ctx t))
  ([def-env ctx t]
   (let [[status ty t'] (type-of-term def-env ctx t)]
     (if (= status :ko)
       (throw (ex-info "Type checking error" ty))
       ty))))

(defn proper-type?
 ([t] (proper-type? defenv/empty-env [] t))
 ([ctx t] (proper-type? defenv/empty-env ctx t))
 ([def-env ctx t]
  (let [ty (type-of def-env ctx t)
        sort (norm/normalize def-env ctx ty)]
    (stx/sort? sort))))
