```clojure
(ns latte-kernel.proof
  "The proof elaborator and checker."
  (:require [latte-kernel.utils :as u]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.typing :as typing]
            [latte-kernel.syntax :as stx]
            [latte-kernel.presyntax :as parse]
            [latte-kernel.norm :as norm]
            [latte-kernel.unparser :as unparser]
            [clojure.pprint :as pp]))

```

 # The Proof checker

 At the lowest level, a LaTTe proof script is represented
 by a sequence of **proof statements**, either:
  - a **variable declaration** `[:declare x T <meta>]` declaring variable `x` of type `T`
  - a **local definition** `[:have <a> T t <meta>]` defining reference `<a>` by term `T` and
    of type `T`  (if inferred then the type is the underscore symbol `_`). The name can be replaced by
    an underscore symbol `_` in which case the definition is not recorded.
  - a **discharge** `[:discharge x <meta>]` of variable `x` (previously introduced by a `:declare` form)
  - a **commitment** `[:qed t <meta>]` yielding the proof term `t` to ultimately submit to the proof checker.

 In all these cases, the `<meta>` argument is a map containing optional metadata.

 The *elaborator* takes a sequence of proof statements, performs incremental checks
 and generate the output term after the `:qed` statement.




 ## Variable declarations

 We begin by the simplest proof statement.


```clojure
(defn elab-declare [def-env ctx var-deps def-uses v ty meta]
  (let [[status, ty'] (typing/rebuild-type def-env ctx ty)]
    (if (= status :ko)
      [:ko ty']
      [:ok [def-env, (cons [v ty'] ctx), (cons [v #{}] var-deps), def-uses]])))


```

 ## Local definitions



```clojure
(declare update-var-deps)
(declare update-def-uses)

;; We make the have step in a small function for "debugging-friendliness".
(declare elab-have-impl)

(defn elab-have [def-env ctx var-deps def-uses name ty term meta]
  ;;(println "  => have step: " name)
  (let [[status res] (elab-have-impl def-env ctx var-deps def-uses name ty term meta)]
    [status res]))

(defn elab-have-impl [def-env ctx var-deps def-uses name ty term meta]
  ;;(println "  => have step: " name)
  (let [[status, term-type, term'] (typing/type-of-term def-env ctx term)]
    (if (= status :ko)
      [:ko {:msg "Have step elaboration failed: cannot synthetize term type."
            :have-name name
            :from term-type
            :meta meta}]
      ;; we have the type here
      (let [[status, rec-ty] (if (= ty '_)
                               [:ok term-type]
                               (let [[status, have-type] (typing/rebuild-type def-env ctx ty)]
                                 (cond
                                   (= status :ko)
                                   [:ko {:msg "Have step elaboration failed: cannot rebuild have-type."
                                         :have-name name
                                         :have-type ty
                                         :error have-type}]
                                   (not (norm/beta-eq? def-env ctx term-type have-type))
                                   [:ko {:msg "Have step elaboration failed: synthetized term type and expected type do not match"
                                         :have-name name
                                         :expected-type have-type ;; or ty ?
                                         :synthetized-type term-type
                                         :meta meta}]
                                   :else
                                   ;;[:ok term-type] ;; XXX: the have-type is mode "declarative" (?)
                                   [:ok have-type])))] ;; largely faster in bad cases !
        (if (= status :ko)
          [:ko (assoc rec-ty :meta meta)]
          (if (= name '_)
            [:ok [def-env ctx var-deps def-uses]]
            (if (defenv/registered-definition? def-env name true)
              [:ko {:msg "Have step elaboration failed: local definition already registered"
                    :have-name name
                    :meta meta}]
              (let [def-env' (defenv/register-definition def-env (defenv/->Definition name [] 0 term rec-ty {}) true)
                    var-deps' (-> var-deps
                                  ;; (update-var-deps name term)
                                  (update-var-deps name rec-ty))
                    def-uses' (-> def-uses
                                  (update-def-uses name term)
                                  (update-def-uses name rec-ty)
                                  (assoc name #{}))]
                [:ok [def-env' ctx var-deps' def-uses']]))))))))

(defn update-var-deps [var-deps name term]
  (let [tvars (stx/free-vars term)]
    (loop [vdeps var-deps, res []]
      (if (seq vdeps)
        (let [[v deps] (first vdeps)]
          ;; (recur (rest vdeps) (conj res [v (if (contains? tvars v)
          ;;                                    (conj deps name)
          ;;                                    deps)]))
          ;; ^^^ old version ^^^
          (recur (rest vdeps) (conj res [v (conj deps name)])))
        res))))

(defn ref-uses-in-term [t]
  (stx/term-reduce {:ref conj} #{} t))

(defn update-def-uses [def-uses name term]
  (let [term-uses (ref-uses-in-term term)]
    (loop [def-uses def-uses, res {}]
      (if (seq def-uses)
        (let [[def-name uses] (first def-uses)]
          (recur (rest def-uses) (assoc res def-name (if (contains? term-uses def-name)
                                                       (conj uses name)
                                                       uses))))
        res))))

```

 ## Variable discharge

 This is the most complex kind of proof step, at least if
 efficiency is a concern (which it is for proof checking)



```clojure
(declare abstract-local-def)
(declare abstract-local-calls)

;; for debugging
(declare elab-discharge-impl)

(defn elab-discharge [def-env ctx var-deps def-uses name meta]
  (if (empty? ctx)
    (throw (ex-info "Context is empty (please report)." {:discharge-name name
                                                         :meta meta}))
    (elab-discharge-impl def-env ctx var-deps def-uses name meta)))

(defn elab-discharge-impl [def-env ctx var-deps def-uses name meta]
  ;; (println "[elab-discharge] name=" name)
  (let [[x ty] (first ctx)]
    (when (not= x name)
      (throw (ex-info "Incorrect discharge name." {:discharge-name name
                                                   :var x
                                                   :meta meta})))
    (let [[x' xdeps] (first var-deps)]
      (when (not= x' x)
        (throw (ex-info "Incorrect discharge name." {:discharge-name name
                                                     :var x'
                                                     :meta meta})))
      (let [def-env' (reduce (fn [def-env def-name]
                               (abstract-local-def def-env def-name x ty)) def-env xdeps)
            def-env'' (reduce (fn [def-env def-name]
                                (abstract-local-calls def-env def-name xdeps x)) def-env' xdeps)]
        [def-env'' (rest ctx) (rest var-deps) def-uses]))))

(defn abstract-local-def [def-env def-name x ty]
  (let [[status, ddef] (defenv/fetch-definition def-env def-name true)]
    (when (= status :ko)
      (throw (ex-info "Local definition not found (please report)" {:def-name def-name})))
    (defenv/register-definition
      def-env (-> ddef
                  (update :params (fn [params] (u/vcons [x ty] params)))
                  (update :arity inc))
      true)))

(declare abstract-local-calls)
(declare gen-local-calls)

(defn abstract-local-calls [def-env ref abs-defs x]
  (let [[status, ddef] (defenv/fetch-definition def-env ref true)]
    (when (= status :ko)
      (throw (ex-info "Local definition not found (please report)" {:def-name ref})))
    (defenv/register-definition
      def-env (-> ddef
                  ;; (update :params (fn [params] (u/vcons [x ty] params)))
                  (update :parsed-term (fn [t] (gen-local-calls t abs-defs x)))) true)))

(defn gen-local-calls [t abs-defs x]
  (cond
    (stx/ref? t) (let [[ref & args] t
                       args' (map #(gen-local-calls % abs-defs x) args)]
                   (cons ref (if (contains? abs-defs ref)
                               (cons x args')
                               args')))
    (stx/binder? t) (let [[binder [y ty] body] t
                          ty' (gen-local-calls ty abs-defs x)
                          body' (gen-local-calls body abs-defs x)]
                      (list binder [y ty'] body'))
    (stx/app? t) (let [[t1 t2] t
                       t1' (gen-local-calls t1 abs-defs x)
                       t2' (gen-local-calls t2 abs-defs x)]
                   [t1' t2'])
    (stx/ascription? t) (let [[e t] t
                              e' (gen-local-calls e abs-defs x)
                              t' (gen-local-calls t abs-defs x)]
                          (list :stx/ascribe e' t'))
    :else t))

```

 ## Proof checking

 All proofs must terminate by a `:qed` action that
 consists in submitting a term and a type.
 The type of the term and the submitted type must
 corresponds, i.e. be equal.


```clojure
(defn elab-qed [def-env ctx term meta]
  (let [[status, proof-type, _] (typing/type-of-term def-env ctx term)]
    (if (= status :ko)
      [:ko {:msg "Qed step failed: cannot infer term type."
            :cause proof-type
            :meta meta}]
      [:ok [def-env term proof-type]])))


;; ## Proof debuggin aids

(defn show-term [t meta]
  (let [pprint? (get meta :pprint true)
        unparse? (get meta :unparse true)]
    (unparser/show-term t pprint? unparse?)))

(defn elab-print-term [def-env ctx term meta]
  (println "============================")
  (let [delta? (get meta :delta true)
        norm? (get meta :norm false)
        term' (if delta?
                (first (norm/delta-step def-env ctx term))
                term)
        term'' (if norm?
                 (norm/beta-red term')
                 term')]
    (println (show-term term'' meta)))
  (println "============================"))

(defn elab-print-type [def-env ctx term meta]
  (println "============================")
  (let [[status ty _] (typing/type-of-term def-env ctx term)
        norm? (get meta :norm false)
        ty' (if norm?
              (norm/beta-red ty)
              ty)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term for print-type."
                      {:term (unparser/unparse term)})))
    (print "type of: ") (println (show-term term meta))
    (println (show-term ty' meta)))
  (println "============================"))


(defn show-def [ddef meta]
  (cond
    (defenv/definition? ddef)
    (str (:params ddef) ":=\n" (show-term (:parsed-term ddef) meta)
         "\n:: " (show-term (:type ddef) meta))
    (or (defenv/theorem? ddef)
        (defenv/axiom? ddef))
    (str (:params ddef) "\n::" (show-term (:type ddef) meta))
    :else
    "<hidden>"))

(defn show-deftype [ddef]
  (cond
    (defenv/definition? ddef) "definition"
    (defenv/axiom? ddef) "axiom"
    (defenv/theorem? ddef) "theorem"
    (defenv/implicit? ddef) "implicit"
    :else "unknown"))

(defn elab-print-def [def-env name meta]
  (println "============================")
  (let [[status ddef] (defenv/fetch-definition def-env name true)]
    (if (= status :ko)
      (println "<<<no such definition>>>")
      (println name (str "(" (show-deftype ddef) "):") (show-def ddef meta))))
  (println "============================"))

(defn elab-print-defenv [def-env meta]
  (println "============================")
  (println "local definitions:")
  (doseq [[name ddef] (defenv/local-definitions def-env)]
    (println name (str "(" (show-deftype ddef) "):") (show-def ddef meta)))
  (println "============================"))

```

 ## Proof elabortation

 The proof elaborator simply iterates over the proof steps
 and dispatch to the adequate elaboration function.

 All the parsing issues are managed by the elaborator.


```clojure
(defn print-state [msg def-env ctx var-deps def-uses]
  (println msg)
  (println "  def-env=" def-env)
  (println "  ctx=" ctx)
  (println "  var-deps=" var-deps)
  (println "  def-uses=" def-uses))

(defn elab-proof-step [def-env ctx var-deps def-uses step args]
  (case step
    :declare
    (let [[v ty-expr meta] args
          [status ty] (parse/parse-term def-env ty-expr)]
      (if (= status :ko)
        [:ko {:msg "Proof failed at declare step: cannot parse type expression."
              :var v
              :type-expr ty-expr
              :meta meta
              :cause ty}]
        (let [[status res] (elab-declare def-env ctx var-deps def-uses v ty meta)]
          (if (= status :ko)
            [:ko res]
            (let [[def-env' ctx' var-deps' def-uses'] res]
              ;; (print-state (str "* Declare step: " (first script))
              ;;              def-env' ctx' var-deps' def-uses')
              [:cont [def-env' ctx' var-deps' def-uses']])))))
    :have
    (let [[name ty-expr term-expr meta] args
          [status-ty ty] (if (= ty-expr '_)
                           [:ok ty-expr]
                           (parse/parse-term def-env ty-expr))
          [status-term term] (parse/parse-term def-env term-expr)]
      (cond
        (= status-ty :ko)
        [:ko {:msg "Proof failed at have step: cannot parse type expression."
              :type-expr ty-expr
              :meta meta
              :cause ty}]
        (= status-term :ko)
        [:ko {:msg "Proof failed at have step: cannot parse term expression."
              :term-expr term-expr
              :meta meta
              :cause term}]
        :else
        (let [[status res] (elab-have def-env ctx var-deps def-uses name ty term meta)]
          (if (= status :ko)
            [:ko res]
            (let [[def-env' ctx' var-deps' def-uses'] res]
              ;; (print-state (str "* Have step: " (first script))
              ;;              def-env' ctx' var-deps' def-uses')
              [:cont [def-env' ctx' var-deps' def-uses']])))))
    :discharge
    (let [[v meta] args
          [def-env' ctx' var-deps' def-uses'] (elab-discharge def-env ctx var-deps def-uses v meta)]
      ;; (print-state (str "* Discharge step: " (first script))
      ;;              def-env' ctx' var-deps' def-uses')
      [:cont [def-env' ctx' var-deps' def-uses']])
    :qed
    (let [[term-expr meta] args
          [status-term term] (parse/parse-term def-env term-expr)]
      (if (= status-term :ko)
        [:ko {:msg "Proof failed at qed step: cannot parse term expression."
              :term-expr term-expr
              :meta meta
              :cause term}]
        (elab-qed def-env ctx term meta)))
    :print-term
    (let [[term-expr meta] args
          [status-term term] (parse/parse-term def-env term-expr)]
      (if (= status-term :ko)
        [:ko {:msg "Proof failed at print step: cannot parse term expression."
              :term-expr term-expr
              :meta meta
              :cause term}]
        (do (elab-print-term def-env ctx term meta)
            [:cont [def-env ctx var-deps def-uses]])))
    :print-type
    (let [[term-expr meta] args
          [status-term term] (parse/parse-term def-env term-expr)]
      (if (= status-term :ko)
        [:ko {:msg "Proof failed at print-type step: cannot parse term expression."
              :term-expr term-expr
              :meta meta
              :cause term}]
        (do (elab-print-type def-env ctx term meta)
            [:cont [def-env ctx var-deps def-uses]])))
    :print-def
    (let [[name meta] args]
      (elab-print-def def-env name meta)
      [:cont [def-env ctx var-deps def-uses]])
    :print-defenv
    (let [[meta] args]
      (elab-print-defenv def-env meta)
      [:cont [def-env ctx var-deps def-uses]])
    ;; else
    (throw (ex-info "Unknown step kind in proof script."
                    {:step step
                     :args args}))))

(defn elab-proof [def-env ctx script]
  (loop [script script, def-env def-env, ctx ctx, var-deps [], def-uses {}]
    (if (seq script)
      (let [[step & args] (first script)
            [status res] (elab-proof-step def-env ctx var-deps def-uses step args)]
        (case status
          :ok (if (seq (rest script))
                (throw (ex-info "Wrong proof script: proof steps after qed."
                                {:script script
                                 :meta meta}))
                [:ok res])
          :ko [:ko res]
          ;; else (continue)
          (let [[def-env' ctx' var-deps' def-uses'] res]
            (recur (rest script) def-env' ctx' var-deps' def-uses'))))
      ;; end of proof script
      [:ko {:msg "Proof incomplete."}])))

(defn compile-proof
  "Compilation of the specified `proof` script. The `goal-assumptions` is a vector of assumptions
  that can be used for the implicit `:assume` steps  (using underscore)."
  ([proof] (compile-proof () proof))
  ([goal-assumptions proof]
   (if (seq proof)
     (do (when (not (seq (first proof)))
           (throw (ex-info "Compilation failed: malformed proof step." {:step (first proof)})))
         (let [[steps goal-assumptions']
               (cond
                 (string? (first proof)) [(list) goal-assumptions]
                 (= (ffirst proof) :assume)
                 (let [[_ meta params & body] (first proof)
                       params (u/zip params)
                       proof-body (compile-proof body)]
                   [(concat (loop [params params, goal-assumptions goal-assumptions, declares []]
                              (if (seq params)
                                (let [[x ty] (first params)]
                                  (if (= ty '_)
                                    ;; the case for implicit assumptions
                                    (if (seq goal-assumptions)
                                      (recur (rest params) (rest goal-assumptions) (conj declares [:declare x (first goal-assumptions) meta]))
                                      (throw (ex-info "Compilation failed: wrong implicit assume step, no such assumption in goal" {:step (first proof)
                                                                                                                                    :assumption x})))
                                    ;; XXX: the first explicit assumption cancels the implicit assumes for the whole proof
                                    (recur (rest params) '() (conj declares [:declare x ty meta]))))
                                declares))
                            proof-body
                            (map (fn [[x _]]
                                   [:discharge x meta]) (reverse params)))
                    ;; no more assumptions after an assume
                    ()])
                 (contains? #{:have :qed :print-term :print-type :print-def :print-defenv} (ffirst proof))
                   ;; XXX: cannot use goal assumptions after a non-assume step
                 [(list (first proof)) ()]
                 :else
                 (throw (ex-info "Compilation failed: unsupported proof step." {:step (first proof)})))]
           ;; in the let
           (concat
            steps
            (compile-proof goal-assumptions' (rest proof)))))
     ;; the end
     (list))))

(defn check-proof
  [def-env ctx thm-name thm-type steps]
  ;;(println "[check proof] " thm-name)
  (let [proof (compile-proof (stx/assumptions thm-type) steps)
        [status res] (elab-proof def-env ctx proof)]
    (if (= status :ko)
      [status res]
      (let [[def-env' proof-term proof-type] res
            [status thm-type'] (typing/rebuild-type def-env' ctx thm-type)]
        (if (= status :ko)
          (throw (ex-info "Cannot rebuild theorem type." {:thm-type thm-type
                                                          :error thm-type'}))
          (if (not (norm/beta-eq? def-env' ctx proof-type thm-type'))
            [:ko {:msg "Theorem type and proof type do not match."
                  :thm-type thm-type'
                  :proof-type proof-type}]
            [:ok [proof-term proof-type]]))))))
```
