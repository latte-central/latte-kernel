```clojure
(ns latte-kernel.syntax
  "The internal representation of lambda-terms."
  (:require [clojure.set :as set]
            [latte-kernel.presyntax :as prestx]))


```

 # The syntax of type theory

 In this namespace we encode the internal representation of
 the lambda-terms.



 ## Lambda terms

 The lambda-terms of LaTTe are composed of:



   - the sorts *kind* `□` and *type* `✳`

```clojure
(defn kind?
  "Is `t` a kind?"
  [t]
  (= t '□))

(defn type?
  "Is `t` a type?"
  [t]
  (= t '✳))

(defn sort?
  "Is `t` a sort?"
  [t]
  (or (kind? t)
      (type? t)))

```

   - occurrences of *variables*

```clojure
(defn variable?
  "Is `t` a variable occurrence?"
  [t]
  (symbol? t))

```

   - *lambda abstractions* `(λ [x t] u)`
   - *product abstractions* `(Π [x t] u)`

```clojure
(defn binder?
  "Is `t` a binding abstraction?"
  [t]
  (and (list? t)
       (contains? '#{λ Π} (first t))))

(defn binderify
  "Generate an abstraction for `binder` from a sequences of `bindings` and a `body`."
  [binder bindings body]
  (loop [bindings (reverse bindings), res body]
    (if (seq bindings)
      (recur (rest bindings) (list binder (first bindings) res))
      res)))

(defn lambda?
  "Is `t` a lambda-abstraction?"
  [t]
  (and (seq? t)
       (= (first t) 'λ)))

(defn prod?
  "Is `t` a product abstraction?"
  [t]
  (and (seq? t)
       (= (first t) 'Π)))

```

  - *applications* `[u v]`

```clojure
(defn app?
  "Is `t` an application?"
  [t]
  (and (vector? t)
       (= (count t) 2)))

(defn appify
  "Build a multiple calls f `f` with `args`."
  [f args]
  (loop [args args, res f]
    (if (seq args)
      (recur (rest args) [res (first args)])
      res)))


```

  - *references* to named definitions `(f {X1 t1, ..., Xn tn} e1 e2 ... eN)`

```clojure
(defn ref?
  "Is `t` a reference?"
  [t]
  (and (seq? t)
       (not (contains? '#{λ Π ::ascribe} (first t)))))

```

  - *ascriptions* `(::ascribe e t)` that term `e` is of type `t`. These are like
 explicit type assertions that are used internally and cannot
 result from parsing a term in the user-level syntax.

 As a safety measure we use the word *ascription* that a user will unlikely
 use its own code. Moreover, the keyword is namespaced so these should
 be enough to emphasis the fact that ascriptions are *dangerous* and
 only used inside the kernel...


```clojure
(defn ascription?
  "Is `t` a type ascription?"
  [t]
  (and (seq? t)
       (= (count t) 3)
       (= (first t) ::ascribe)))

```

 Note that type ascriptions do not add any expressivity, but
 they allow interesting optimizations (ascribed types do not need
 to be recomputed).


```clojure
(defn host-constant?
  "Is `t` a constant provided by the host?"
  [t]
  (and (vector? t)
       (= (count t) 2)
       (= (first t) ::prestx/host-constant)))

```

 ... and that's everything you need to capture the
 essence of mathematics!


```clojure
(defn term?
  "Checks if `v` is a LaTTe term."
  [v]
  (or (sort? v)
      (variable? v)
      (binder? v)
      (app? v)
      (ref? v)
      (ascription? v)
      (host-constant? v)))

```

 ## Term reducer

 A reducer for terms.



```clojure
(defn term-reduce [red-funs init t]
  (cond
    (host-constant? t) t
    (kind? t) (if-let [kind-fn (get red-funs :kind)]
                (kind-fn init)
                init)
    (type? t) (if-let [type-fn (get red-funs :type)]
                (type-fn init)
                init)
    (variable? t) (if-let [var-fn (get red-funs :var)]
                    (var-fn init t)
                    init)
    (binder? t) (let [[_ [x ty] body] t
                      bind-kind (if (lambda? t) :lambda :prod)
                      ty-val (term-reduce red-funs init ty)
                      body-val (term-reduce red-funs ty-val body)]
                  (if-let [binder-fn (get red-funs bind-kind)]
                    (binder-fn body-val x)
                    body-val))
    (app? t) (let [[t1 t2] t
                   val1 (term-reduce red-funs init t1)
                   val2 (term-reduce red-funs val1 t2)]
               (if-let [app-fn (get red-funs :app)]
                 (app-fn val2)
                 val2))
    (ascription? t) (let [[t1 t2] t
                          val1 (term-reduce red-funs init t1)
                          val2 (term-reduce red-funs val1 t2)]
                      (if-let [asc-fn (get red-funs :ascribe)]
                        (asc-fn val2)
                        val2))
    (ref? t) (let [[dname & args] t
                   args-val (reduce (fn [val arg]
                                      (term-reduce red-funs val arg)) init args)]
               (if-let [ref-fn (get red-funs :ref)]
                 (ref-fn args-val dname)
                 args-val))
    :else (throw (ex-info "Cannot term reduce: unknown (sub-)term" {:term t}))))

```

 ## Free and bound variables

 In `(lambda [x t] [x y])` there is one *bound occurrence* of
 variable `x` and one *free occurrence* of variable `y`.


```clojure
(defn free-vars
  "Get the set of free variables of term `t`."
  [t]
  (cond
    (variable? t) #{t}
    (binder? t) (let [[_ [x ty] body] t]
                  (set/union (free-vars ty)
                             (disj (free-vars body) x)))
    (app? t) (set/union (free-vars (first t))
                        (free-vars (second t)))
    (ascription? t) (let [[_ e u] t]
                     (set/union (free-vars e)
                                (free-vars u)))
    (ref? t) (apply set/union (map free-vars (rest t)))
    :else #{}))

(defn vars
  "Get the set of free and bound variables of term `t`."
  [t]
  (cond
    (variable? t) #{t}
    (binder? t) (let [[_ [x ty] body] t]
                  (set/union (vars ty) (vars body)))
    (app? t) (set/union (vars (first t))
                        (vars (second t)))
    (ascription? t) (let [[_ e u] t]
                     (set/union (vars e) (vars u)))
    (ref? t) (apply set/union (map vars (rest t)))
    :else #{}))

(defn bound-vars
  "Get the set of bound variables of term `t`."
  [t]
  (set/difference (vars t) (free-vars t)))

```

 ## Substitution

 The substitution of free occurrences of variables by
 terms might be thought of as a simple thing but it is *not*.
 The algorithm is rather tricky because one has to avoid
 nameclash. Instead of a locally-nameless solution, which yields
 a much simpler algorithm we rely on an explicit renaming scheme,
 quite similar to what can be found in e.g. HOL light.

 The advantage of explicit renaming is that it is much more
 robust in further algorithms (especially type inference which
 is very cumbersome with nameless representations).


```clojure
(defn mk-fresh
  "Generate a fresh variable name, with prefix `base`
  and suffix chosen from ' (quote), '', ''' then -4, -5, etc.
  The `forbid` argument says what names are forbidden."
  ([base forbid] (mk-fresh base 0 forbid))
  ([base ^long level forbid]
   (let [suffix (case level
                  0 ""
                  1 "'"
                  2 "''"
                  3 "'''"
                  (str "-" level))
         candidate (symbol (str base suffix))]
     (if (contains? forbid candidate)
       (recur base (inc level) forbid)
       candidate))))

```

 The following is the core of the substitution algorithm.


```clojure
(declare rebinder)

(defn- subst-
  "Applies substituion `sub` on term `t`.
  Names generated fresh along the substitution cannot be members of `forbid`.
  Bound variable may be renamed according to the `rebind` map."
  [t sub forbid rebind]
  (let [[t' forbid']
        (cond
          ;; variables
          (variable? t) (if-let [x (get rebind t)]
                          [x (conj forbid t)]
                          [(get sub t t) (conj forbid t)])
          ;; binders (λ, Π)
          (binder? t)
          (let [[binder [x ty] body] t
                [x' rebind' forbid'] (rebinder x rebind forbid)
                [ty' forbid''] (subst- ty sub forbid' rebind)
                [body' forbid'''] (subst- body sub forbid'' rebind')]
            ;; (println "term=" (list binder [x' ty'] body') "sub=" sub')
            [(list binder [x' ty'] body')
             forbid'''])
          ;; applications
          (app? t)
          (let [[rator forbid'] (subst- (first t) sub forbid rebind)
                [rand forbid''] (subst- (second t) sub forbid' rebind)]
            [[rator rand] forbid''])
          ;; ascriptions
          (ascription? t)
          (let [[_ e u] t
                [e' forbid'] (subst- e sub forbid rebind)
                [u' forbid''] (subst- u sub forbid' rebind)]
            [(list ::ascribe e' u') forbid''])
          ;; references
          (ref? t) (let [[args forbid']
                         (reduce (fn [[ts forbid] t]
                                   (let [[t' forbid'] (subst- t sub forbid rebind)]
                                     [(conj ts t') forbid'])) ['() forbid] (rest t))]
                     [(conj (into '() args) (first t)) forbid'])
          ;; other cases
          :else [t forbid])]
    ;;(println "[subst-] t=" t "sub=" sub "forbid=" forbid "rebind=" rebind)
    ;;(println "   ==> " t')
    [t' forbid']))

(defn rebinder
  "Rebind `x` if it is present in `forbid`."
  [x rebind forbid]
  (if (contains? forbid x)
    (let [x' (mk-fresh x forbid)]
      [x' (assoc rebind x x') (conj forbid x')])
    [x rebind (conj forbid x)]))


(defn subst
  "Applies substitution `sub` (defaulting to `{x u}`) to term `t`."
  ([t x u] (subst t {x u}))
  ([t sub]
   (let [forbid (apply set/union
                  (into #{} (keys sub))
                  (free-vars t)
                  (map vars (vals sub)))
         [t' _] (subst- t sub forbid {})]
     t')))

```

 ## Alpha-equivalence

 Comparing lambda-terms should be up to *alpha-equivalence*.
 To recover a structural equality, a nameless representation
 of lambda-terms can be used. Each bound variable is renamed
 in a canonical way using so-called *Debruijn indices*.

 The normalization process is described below.


```clojure
(defn- alpha-norm- [t sub level]
  (cond
    ;; variables
    (variable? t) [(get sub t t) level]
    ;; binders (λ, Π)
    (binder? t)
    (let [[binder [x ty] body] t
          x' (symbol (str "_" level))
          [ty' level'] (alpha-norm- ty sub (inc level))
          [body' level''] (alpha-norm- body (assoc sub x x') level')]
      [(list binder [x' ty'] body')
       level''])
    ;; applications
    (app? t)
    (let [[left' level'] (alpha-norm- (first t) sub level)
          [right' level''] (alpha-norm- (second t) sub level')]
      [[left' right'] level''])
    ;; ascription
    (ascription? t)
    (let [[_ e _] t
          [e' level'] (alpha-norm- e sub level)]
          ;; the type part is removed during alpha-normalization
      [e' level'])
    ;; references
    (ref? t) (let [[args level']
                   (reduce (fn [[args level] arg]
                             (let [[arg' level'] (alpha-norm- arg sub level)]
                               [(conj args arg') level'])) ['() level] (rest t))]
               [(conj (into '() args) (first t)) level'])
    ;; other cases
    :else [t level]))

(defn alpha-norm
  "Produce a canonical nameless representation of the lambda-term `t`"
  [t]
  (let [[t' _] (alpha-norm- t {} 1)]
    t'))

```

 Now alpha-equivalence of lambda-terms simply
 boils down to the equality of their nameless representation.


```clojure
(defn alpha-eq? [t1 t2]
  (= (alpha-norm t1)
     (alpha-norm t2)))


```

 ## Assumptions

 The next facility is to extract assumptions from a given term.
 An assumption is simply the type of a product variable.
 e.g. in `(Π [x T] U)` the top-level assumption is the expression `T`.


```clojure
(defn top-assumption
  "Fetch the top-level assumption of term `t` if its a product,
  and returns a pair composed of the assumption and the remaining of the term.
  Otherwise returns `[nil t]`."
  [t]
  (if (prod? t)
    (let [[_ [_ ty] body] t]
      [ty body])
    [nil t]))

(defn assumptions
  "Fetch all the assumptions of term `t` as a vector. The vector
  is of course empty if there is no such assumption."
  [t]
  (loop [t t, v []]
    (let [[top t'] (top-assumption t)]
      (if (nil? top)
        v
        (recur t' (conj v top))))))
```
