(ns latte-kernel.norm
  "Normalization and beta-equivalence."
  (:require [latte-kernel.syntax :as stx]
            [latte-kernel.defenv :as defenv :refer [definition? theorem? axiom?]]
            [latte-kernel.nbe :as nbe]
            [latte-kernel.unparser :as u]))

;; XXX: while we experiment with
;; the normalization-by-evaluation schemen,
;; we keep the (compile-time) possibility of
;; switching to the old symbolic normalization
;; scheme (`:beta-norm`).
(def norm-type
  #_:beta-norm
  :nbe
  #_:both
  #_:all)

;;{
;; # Normalization
;;
;; The semantics of the lambda-calculus relies on a fundamental rewrite rule: *beta-reduction*.
;;
;; The process of *normalization* is the repeated application of the beta-reduction rule until
;; it is not possible to do so. A normalization algorithm applies a *rewrite strategy* to
;; apply the beta-reductions in some (most often) deterministic way.
;;
;; Because LaTTe extends the λ-calculus with explicit definitions, a dedicated rewriting process
;; is defined for unfolding definitions when needed. This is based on another reduction rule
;; named *delta-reduction*.
;;
;; Thus unlike the classical λ-calculus, we need to handle three reduction principles at once
;; in the normalization process.
;;
;; A type theory requires the normalization process to ensure two fundamental propertie:
;;
;;   1. *strong normalization*: it is not possible to rewrite a given term infinitely, which
;;   means that the normalization algorithm must terminate.
;;
;;   2. *confluence*: different strategies can be followed for reducing a given term -
;;   the normalization process is non-deterministics - but the ultimate result must be the same (up-to alpha-equivalence)
;;
;; Strong normalization is as its name implies a very strong constraint, and in general
;; separate λ-calculi aimed at logical reasoning - that enjoy the property - and those
;; that are aimed at programming - for which the requirement is much too strong because
;; partial functions are not supported. Confluence in the programming case is associated
;; to a given strategy: strict or lazy (sometimes associated to a form of parallelism).
;; In the logic case, the normalization process is confluent regardless of the chosen strategy.
;;
;;
;; The LaTTe calculus is a type theory aimed at logical reasoning and thus enjoys the two properties.
;; There is no formal proof of it, but despite all of our effort we never observed any failure
;; as of today. Moreover, the formal definition of the calculus is available in the
;; *Type Theory and Formal Proof: an Introduction* (TTFP) book. There strong normalization and
;; confluence are discussed at length.
;;
;; By way of consequence, for each term `t` the normalization process produces a term `t'` that
;; is unique up-to alpha-equivalence. This term is named the *normal form* of `t`.
;;
;; We will now describe the normalization process in details.
;;
;;}



;;{
;; ## Beta-reduction

;; At the heart of a λ-calculus lies *beta-reduction*.
;; The reduction rule is based on a principle of substitution for (free occurrences of) variables
;; by arbitrary terms, which is far from being a simple thing.

;; Here is an example of a somewhat tricky example (resulting from an old tricky bug in the LaTTe kernel):

;; ```
;;  ((lambda [z :type] (lambda [x :type] (x y))) x)
;;   ~~> (lambda [x :type] (x x)    is wrong
;;
;;   ((lambda [z :type] (lambda [x :type] (x z))) x)
;; = ((lambda [z :type] (lambda [y :type] (y z))) x)
;;   ~~> (lambda [y :type] (y x)    is correct
;; ```
;;
;; What is called a *redex* (reducible expression) is simply the application of
;; a λ-abstraction on a term.
;;}

(defn redex?
  "Is `t` a reducible expression ?"
  [t]
  (and (stx/app? t)
       (stx/lambda? (first t))))

(defn ^{:deprecated "use nbe instead"} beta-reduction
  "The basic rule of *beta-reduction* for term `t`.
  Note that the term `t` must already be a *redex*
  so that the rewrite can be performed."
  [t]
  (if (redex? t)
    (let [[[_ [x _] body] rand] t]
      (stx/subst body x rand))
    (throw (ex-info "Cannot beta-reduce. Not a redex" {:term t}))))

;;{
;; #### The normalization strategy
;;
;; The most important principle in the normalization process
;; is the way *redexes* are discovered. For this, a *strategy*
;; must be implemented. It is a kind of a *black art* of not
;; spending too much time looking for them, but also ensuring
;; that all of them are found. LaTTe focuses on the latter.
;;}

(declare beta-step-args)

(defn  ^{:deprecated "use nbe instead"} beta-step
  "A call to this function will reduce a (somewhat)
  arbitrary number of *redexes* in term `t`
  using a mostly bottom-up strategy, and reducing
  all terms at the same level (e.g. definition arguments).

  The return value is a pair `[t' red?]` with `t'` the
  potentially rewritten version of `t` and `red?` is `true`
  iff at least one redex was found and reduced."
  ([t] (beta-step t 0))
  ([t rcount]
   (cond
     ;; binder
     (stx/binder? t)
     (let [[binder [x ty] body] t
           ;; 1) try reduction in binding type
           [ty' rcount1] (beta-step ty rcount)
           ;; 2) also try reduction in body
           [body' rcount2] (beta-step body rcount1)]
       [(list binder [x ty'] body') rcount2])
     ;; application
     (stx/app? t)
     (let [[left right] t
           ;; 1) try left reduction
           [left' rcount1] (beta-step left rcount)
           ;; 2) also try right reduction
           [right' rcount2] (beta-step right rcount1)]
       (if (stx/lambda? left')
         ;; we have a redex
         (recur (beta-reduction [left' right']) (inc rcount2))
         ;; or we stay with an application
         [[left' right'] rcount2]))
     ;; reference
     (stx/ref? t)
     (let [[def-name & args] t
           [args' rcount'] (beta-step-args args rcount)]
       (if (not= rcount' rcount)
         (recur (list* def-name args') rcount')
         [t rcount]))
     ;; ascriptions
     (stx/ascription? t)
     (let [[_ ty term] t
           [ty' rcount1] (beta-step ty rcount)
           [term' rcount2] (beta-step term rcount1)]
       [(list :latte-kernel.syntax/ascribe ty' term') rcount2])
     ;; other cases
     :else [t rcount])))

(defn  ^{:deprecated "use nbe instead"} beta-step-args
  "Apply the reduction strategy on the terms `ts`
  in *\"parallel\"*. This is one place
  where many redexes can be found at once.
  This returns a pair composed of the rewritten
  terms and a flag telling if at least one reduction
  took place."
  [ts rcount]
  (loop [ts ts, ts' [], rcount rcount]
    (if (seq ts)
      (let [[t' rcount'] (beta-step (first ts) rcount)]
        (recur (rest ts) (conj ts' t') rcount'))
      [ts' rcount])))

(defn  ^{:deprecated "use nbe instead"} beta-red
  "Reduce term `t` according to the normalization strategy."
  [t]
  (case norm-type
    :beta-norm (first (beta-step t))
    :nbe (nbe/norm t)
    :both (let [[beta-t _] (beta-step t)
                nbe-t (nbe/norm t)]
            (if (stx/alpha-eq? beta-t nbe-t)
              beta-t
              (throw (ex-info "Terms not alpha-equivalent in beta-red."
                       {:original t, :beta-term beta-t, :nbe-term nbe-t}))))
    :all (let [[beta-t _] (beta-step t)
                nbe-t (nbe/norm t)
                readable-t (stx/readable-term nbe-t)]
           (if (stx/alpha-eq? beta-t nbe-t)
             (if (stx/alpha-eq? beta-t readable-t)
               beta-t
               (throw (ex-info "Term not actually readable in beta-red."
                        {:original t, :beta-term beta-t
                         :nbe-term nbe-t, :readable-term readable-t})))
             (throw (ex-info "Terms not alpha-equivalent in beta-red."
                      {:original t, :beta-term beta-t, :nbe-term nbe-t}))))))

;;{
;; ## Delta-reduction (unfolding of definitions)
;;
;; If beta-reduction is at the heart of computing with
;; values in the lambda-calculus, the *delta-reduction* is
;; the corresponding principle for computing with *names*.
;;
;; From the point of view of calculability, names are not
;; needed: they don't add any expressive power to the
;; language. As such, they are not part of the theoretical
;; lambda-calculus. However in practice, names play a
;; central role in computation.
;;
;; From the point of view of LaTTe, the use of names
;; is important for two reasons:
;;
;;   1. Mathematical definitions and theorems need to be named so that they can
;;  be further referenced, that's a basic fact of mathematics.
;;
;;   2. Named computation can be performed much more efficiently than relying
;; on beta-reduction, this will be made clear later on.
;;
;; The rewrite rule of delta-reduction corresponds to the unfolding
;; of a pameterized definition, based on the substitution of the parameters
;; by actual arguments. The process is called *instantiation*.
;;}

(defn ^{:deprecated "use nbe instead"} instantiate-def
  "Substitute in the `body` of a definition the parameters `params`
  by the actual arguments `args`."
  [params body args]
  ;;(println "[instantiate-def] params=" params "body=" body "args=" args)
  (loop [args args, params params, sub {}]
    (if (seq args)
      (if (empty? params)
        (throw (ex-info "Not enough parameters (please report)" {:args args}))
        (recur (rest args) (rest params) (assoc sub (ffirst params) (first args))))
      (loop [params (reverse params), res body]
        (if (seq params)
          (recur (rest params) (list 'λ (first params) res))
          (stx/subst res sub))))))

;;{
;; Note that for the sake of efficiency, we do not unfold theorems (by their proof)
;; hence at the computational level a theorem is not equivalent to its proof, which
;; is of course a good thing because of *proof irrelevance*. However an error is
;; raised if one tries to reduce with a yet unproven theorem.
;;}

;; This is to solve a *real* (and rare) use case for circular dependency
(def +unfold-implicit+ (atom nil))
(defn install-unfold-implicit!
  [unfold-fn]
  (reset! +unfold-implicit+ unfold-fn)
  (reset! nbe/+unfold-implicit+ unfold-fn))

(defn  ^{:deprecated "use nbe instead"} delta-reduction
  "Apply a strategy of delta-reduction in definitional environment `def-env`, context `ctx` and
  term `t`. If the flag `local?` is `true` the definition in only looked for
  in `def-env`. By default it is also looked for in the current namespace (in Clojure only)."
  ([def-env ctx t] (delta-reduction def-env ctx t false))
  ([def-env ctx t local?]
   ;; (println "[delta-reduction] t=" t)
   (if (not (stx/ref? t))
     (throw (ex-info "Cannot delta-reduce: not a reference term (please report)." {:term t}))
     (let [[name & args] t
           [status sdef]  (defenv/fetch-definition def-env name local?)]
       ;; (println "[delta-reduction] term=" t "def=" sdef)
       (cond
         (= status :ko) ;; [t false] ;; No error?
         (throw (ex-info "No such definition" {:term t :def-name name}))
         (defenv/implicit? sdef)
         ;; (throw (ex-info "Cannot delta-reduce an implicit (please report)." {:term t}))
         (let [[status, implicit-term, _] (@+unfold-implicit+ def-env ctx sdef args)]
           (if (= status :ko)
             (throw (ex-info "Cannot delta-reduce implicit term." implicit-term))
             [implicit-term true]))
         (> (count args) (:arity sdef))
         (throw (ex-info "Too many arguments to instantiate definition."
                         {:term t :def-name name :nb-params (:arity sdef) :nb-args (count args)}))
         (definition? sdef)
         ;; unfolding a defined term
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
           (throw (ex-info "Cannot use theorem with no proof." {:term t :theorem sdef})))
         (axiom? sdef) [t false]
         ;; nothing known
         :else (throw (ex-info "Not a Latte definition (please report)."
                               {:term t :def sdef})))))))

;;{
;; ### Delta-reduction strategy
;;
;; The strategy we adopt for delta-reduction is close to the one usesd
;; for beta-reduction. Of course we are not looking for beta but *delta-redexes*,
;;  i.e. *"call"* to definitions.
;;}

(declare delta-step-args)

(defn  ^{:deprecated "use nbe instead"} delta-step
  "Applies the strategy of *delta-reduction* on term `t` with definitional
  environment `def-env`. If the optional flag `local?` is `true` only the
  local environment is used, otherwise (the default case) the definitions
  are also searched in the current namespace (in Clojure only)."
  ([def-env ctx t] (delta-step def-env ctx t false 0))
  ([def-env ctx t local?] (delta-step def-env ctx t local? 0))
  ([def-env ctx t local? rcount]
   ;; (println "[delta-step] t=" t)
   (cond
     ;; binder
     (stx/binder? t)
     (let [[binder [x ty] body] t
           ;; 1) try reduction in binding type
           [ty' rcount1] (delta-step def-env ctx ty local? rcount)
           ;; 2) also try reduction in body
           [body' rcount2] (delta-step def-env (cons [x ty'] ctx) body local? rcount1)]
       [(list binder [x ty'] body') rcount2])
     ;; application
     (stx/app? t)
     (let [[left right] t
           ;; 1) try left reduction
           [left' rcount1] (delta-step def-env ctx left local? rcount)
           ;; 2) also try right reduction
           [right' rcount2] (delta-step def-env ctx right local? rcount1)]
       [[left' right'] rcount2])
     ;; reference
     (stx/ref? t)
     (let [[def-name & args] t
           [t' red?] (delta-reduction def-env ctx t)]
       (if red?
         (recur def-env ctx t' local? (inc rcount))
         ;; only reduce the arguments if the top is not a delta-redex (but still a reference)
         (let [[args' rcount'] (delta-step-args def-env ctx args local? rcount)]
           [(list* def-name args') rcount'])))
     ;; ascription
     (stx/ascription? t)
     (let [[_ ty term] t
           [ty' rcount1] (delta-step def-env ctx ty local? rcount)
           [term' rcount2] (delta-step def-env ctx term local? rcount1)]
       [(list :latte-kernel.syntax/ascribe ty' term') rcount2])
     ;; other cases
     :else [t rcount])))

(defn  ^{:deprecated "use nbe instead"} delta-step-args
  "Applies the delta-reduction on the terms `ts`."
  [def-env ctx ts local? rcount]
  (loop [ts ts, ts' [], rcount rcount]
    (if (seq ts)
      (let [[t' rcount'] (delta-step def-env ctx (first ts) local? rcount)]
        (recur (rest ts) (conj ts' t') rcount'))
      [ts' rcount])))

;;{
;; ## Normalization
;;
;; We finally define a few normalization functions:
;;   - normalize using beta-reduction only: [[beta-normalize]]
;;   - normalize using delta-reduction only: [[delta-normalize]]
;;   - normalize using delta-reduction with the local environment only: [[delta-normalize-local]]
;;}

(defn  ^{:deprecated "use nbe instead"} delta-normalize
  "Normalize term `t` for delta-reduction."
  [def-env ctx t]
  (let [[t' rcount] (delta-step def-env ctx t)]
    ;;(println "[INFO] Number of delta-reductions=" rcount)
    t'))

(defn  ^{:deprecated "use nbe instead"} delta-normalize-local
  "Normalize term `t` for delta-reduction using only
  environment `def-env` (and *not* the current namespace)."
  [def-env ctx t]
  (let [[t' rcount] (delta-step def-env ctx t true)]
    ;;(println "[INFO] Number of (local) delta-reductions=" rcount)
    t'))

;;{
;; The heart of the general normalization process is
;; the following function. It orders the strategies
;; in the following way:
;;   1. apply delta-reduction first
;;   3. then apply beta-reduction
;;   4. try again the whole process if the term was rewritten
;;      or just return the result.
;;
;; The LaTTe *normal forms* are defined by this function, i.e.
;; these are the terms for which the function acts as an identity.
;; This is a formal definition, but its mathematical properties
;; are not easy to derive from the code. However it has been
;; thoroughly tested. It is also *safe* in the sense that at worst
;; it will lead to too many distinctions, but there is no risk
;; of confusion.
;;
;; **Remark**: some optimizations could be performed here, but
;; we found out that even small change in this definition
;; could easily lead to dramatic effects, so we are very
;; conservative in this part of the kernel.
;;}

(defn beta-delta-normalize
  "Apply the general normalization strategy of LaTTe on term `t`.
  The result is defined as *the normal form* of `t`."
  [def-env ctx t]
  ;;(println "[beta-delta-normalize]: t=" t)
  (case norm-type
    :nbe (nbe/norm def-env ctx t)
    ;; XXX: The alternative schemes below are deprecated
    :beta-norm (first (beta-step (first (delta-step def-env ctx t))))
    :both (let [[beta-t _] (beta-step (first (delta-step def-env ctx t)))
                nbe-t (nbe/norm def-env ctx t)]
            (if (stx/alpha-eq? beta-t nbe-t)
              beta-t
              (throw (ex-info "Terms not alpha-equivalent in beta-delta-norm."
                       {:original t, :beta-term beta-t, :nbe-term nbe-t
                        :def-env def-env, :ctx ctx}))))
    :all (let [[beta-t _] (beta-step (first (delta-step def-env ctx t)))
                nbe-t (nbe/norm def-env ctx t)
                readable-t (stx/readable-term nbe-t)]
           (if (stx/alpha-eq? beta-t nbe-t)
             (if (stx/alpha-eq? beta-t readable-t)
               beta-t
               (throw (ex-info "Term not actually readable in beta-red."
                        {:original t, :beta-term beta-t
                         :nbe-term nbe-t, :readable-term readable-t})))
             (throw (ex-info "Terms not alpha-equivalent in beta-red."
                      {:original t, :beta-term beta-t, :nbe-term nbe-t}))))))
;;{
;; The following is the main user-level function for normalization.
;;}

(defn normalize
  "Normalize term `t` in (optional) environment `def-env` and (optional) context `ctx`.
  The result is *the normal form* of `t`."
  ([t] (normalize defenv/empty-env [] t))
  ([def-env t] (normalize def-env [] t))
  ([def-env ctx t] (beta-delta-normalize def-env ctx t)))

;;{
;; ## Beta-equivalence
;;
;; The main objective of having a normalization algorithm is to be
;; able to compare terms for a dedicated notion of equivalence.
;; In the lambda-calculus this is generally called *beta-equivalence*
;; and we will convey the same name here. However it is clear that
;; we also mean equivalent for our general normalization procedure
;; (involving delta also).
;; Note also that the resulting normal forms are compared for
;; alpha-equivalence so that bound variables do not get in the way.
;;}

(defn beta-eq?
  "Are terms `t1` and `t2` equivalent, i.e. with the
  same normal form (up-to alpha-convertion)?"
  ([t1 t2]
   (let [t1' (normalize t1)
         t2' (normalize t2)]
     (stx/alpha-eq? t1' t2')))
  ([def-env t1 t2]
   (let [t1' (normalize def-env t1)
         t2' (normalize def-env t2)]
     (stx/alpha-eq? t1' t2')))
  ([def-env ctx t1 t2]
   (let [t1' (normalize def-env ctx t1)
         t2' (normalize def-env ctx t2)]
     ;;(println "t1' = " (u/show-term t1'))
     ;;(println "t2' = " (u/show-term t2'))
     (stx/alpha-eq? t1' t2'))))
