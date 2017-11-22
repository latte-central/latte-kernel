(ns latte-kernel.proof
  "The proof elaborator and checker."
  (:require [latte-kernel.utils :as u]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.typing :as typing]
            [latte-kernel.syntax :as stx]
            [latte-kernel.presyntax :as parse]
            [latte-kernel.norm :as norm]
            [latte-kernel.unparser :as unparser]
            [latte-kernel.defs :refer [mkdef]]
            [clojure.pprint :as pp]))

;;{
;; # The Proof checker
;;
;; At the lowest level, a LaTTe proof script is represented
;; by a sequence of **proof statements**, either:
;;  - a **variable declaration** `[:declare x T <meta>]` declaring variable `x` of type `T`
;;  - a **local definition** `[:have <a> T t <meta>]` defining reference `<a>` by term `T` and
;;    of type `T`  (if inferred then the type is the underscore symbol `_`). The name can be replaced by
;;    an underscore symbol `_` in which case the definition is not recorded.
;;  - a **discharge** `[:discharge x <meta>]` of variable `x` (previously introduced by a `:declare` form)
;;  - a **commitment** `[:qed t <meta>]` yielding the proof term `t` to ultimately submit to the proof checker.
;;
;; In all these cases, the `<meta>` argument is a map containing optional metadata.
;;
;; The *elaborator* takes a sequence of proof statements, performs incremental checks
;; and generate the output term after the `:qed` statement.
;;
;;}

;;{
;; ## Variable declarations
;;
;; We begin by the simplest proof statement.
;;}

(defn elab-declare [def-env ctx var-deps def-uses v ty meta]
  (let [[status, ty'] [:ok ty];; was: (typing/rebuild-type def-env ctx ty)
        ]
    (if (= status :ko)
      [:ko ty']
      [:ok [def-env, (cons [v ty'] ctx), (cons [v #{}] var-deps), def-uses]])))

;;{
;; ## Local definitions
;;
;;}

(declare update-var-deps)
(declare update-def-uses)

(defn elab-have [def-env ctx var-deps def-uses name ty term meta]
  (println "  => have step: " name)
  (let [[status, term-type, term'] (typing/type-of-term def-env ctx term)]
    (if (= status :ko)
      [:ko {:msg "Have step elaboration failed: cannot synthetize term type."
            :have-name name
            :from term-type
            :meta meta}]
      ;; we have the type here
      (let [[status, rec-ty] (if (= ty '_)
                               [:ok term-type]
                               (let [[status, have-type] [:ok ty];; was: (typing/rebuild-type def-env ctx ty)
                                     ]
                                 (cond
                                   (= status :ko)
                                   [:ko {:msg "Have step elaboration failed: cannot rebuild have-type."
                                         :have-name name
                                         :have-type ty
                                         :error have-type}]
                                   (not (norm/beta-eq? def-env ctx term-type have-type))
                                   [:ko {:msg "Have step elaboration failed: synthetized term type and expected type do not match"
                                         :have-name name
                                         :expected-type ty ;; or have-type ?
                                         :synthetized-type term-type
                                         :meta meta}]
                                   :else
                                   ;;[:ok term-type] ;; XXX: the have-type is mode "declarative" (?)
                                   [:ok have-type] ;; largely faster in bad cases !
                                   )))]
        (if (= status :ko)
          [:ko (assoc rec-ty :meta meta)]
          (if (= name '_)
            [:ok [def-env ctx var-deps def-uses]]
            (if (defenv/registered-definition? def-env name true)
              [:ko {:msg "Have step elaboration failed: local definition already registered"
                    :have-name name
                    :meta meta}]
              (let [def-env' (defenv/register-definition def-env (mkdef name [] term rec-ty {}) true)
                    var-deps' (-> var-deps
                                  ;; (update-var-deps name term)
                                  (update-var-deps name rec-ty))
                    def-uses'(-> def-uses
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
          (recur (rest vdeps) (conj res [v (conj deps name)]))
          )
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

;;{
;; ## Variable discharge
;;
;; This is the most complex kind of proof step, at least if
;; efficiency is a concern (which it is for proof checking)
;;
;;}

(declare abstract-local-def)
(declare abstract-local-calls)

(defn elab-discharge [def-env ctx var-deps def-uses name meta]
  ;; (println "[elab-discharge] name=" name)
  (when (empty? ctx)
    (throw (ex-info "Context is empty (please report)." {:disacharge-name name
                                                         :meta meta})))
  (let [[x _] (first ctx)]
    (when (not= x name)
      (throw (ex-info "Incorrect discharge name." {:discharge-name name
                                                   :var x
                                                   :meta meta})))
    (let [[status ty _] (typing/type-of-term def-env ctx x)]
      (when (= status :ko)
        (throw (ex-info "Cannot recompute type of context variable." {:variable x
                                                                      :error ty})))
      (let [[x' xdeps] (first var-deps)]
        (when (not= x' x)
          (throw (ex-info "Incorrect discharge name." {:discharge-name name
                                                       :var x'
                                                       :meta meta})))
        (loop [def-env def-env, abstracted-deps #{}, deps xdeps]
          (if (seq deps)
            (let [def-env' (if (contains? abstracted-deps (first deps))
                             def-env
                             (abstract-local-def def-env (first deps) x ty))
                  def-env'' (abstract-local-calls def-env' (first deps) abstracted-deps x)
                  deps' (into (get def-uses (first deps) #{}) (rest  deps))]
              (recur def-env'' (conj abstracted-deps (first deps)) deps'))
            [def-env (rest ctx) (rest var-deps) def-uses]))))))

(defn abstract-local-def [def-env def-name x ty]
  (let [[status, ddef] (defenv/fetch-definition def-env def-name true)]
    (when (= status :ko)
      (throw (ex-info "Local definition not found (please report)" {:def-name def-name})))
    (defenv/register-definition def-env (update ddef :params (fn [params] (u/vcons [x ty] params))) true)))

(declare abstract-local-calls)
(declare gen-local-calls)

(defn abstract-local-calls [def-env ref abs-defs x]
  (let [[status, ddef] (defenv/fetch-definition def-env ref true)]
    (when (= status :ko)
      (throw (ex-info "Local definition not found (please report)" {:def-name ref})))
    (defenv/register-definition def-env (-> ddef
                                            ;; (update :params (fn [params] (u/vcons [x ty] params)))
                                            (update :parsed-term (fn [t] (gen-local-calls t abs-defs x)))) true)))

(defn gen-local-calls [t abs-defs x]
  (cond
    (stx/ref? t) (let [[ref & args] t
                       args' (map #(gen-local-calls % abs-defs x) args)]
                   (cons ref (if (contains? abs-defs ref)
                               (cons x args')
                               args')))
    (stx/binder? t) (let [[_ [x ty] body] t
                          ty' (gen-local-calls ty abs-defs x)
                          body' (gen-local-calls body abs-defs x)]
                      (if (stx/lambda? t)
                        (list 'λ [x ty'] body')
                        (list 'Π [x ty'] body')))
    (stx/app? t) (let [[t1 t2] t
                       t1' (gen-local-calls t1 abs-defs x)
                       t2' (gen-local-calls t2 abs-defs x)]
                   [t1' t2'])
    (stx/ascription? t) (let [[e t] t
                              e' (gen-local-calls e abs-defs x)
                              t' (gen-local-calls t abs-defs x)]
                          (list :stx/ascribe e' t'))
    :else t))

;;{
;; ## Proof checking
;;
;; All proofs must terminate by a `:qed` action that
;; consists in submitting a term and a type.
;; The type of the term and the submitted type must
;; corresponds, i.e. be equal.
;;}

(defn elab-qed [def-env ctx term meta]
  (let [[status, proof-type, _] (typing/type-of-term def-env ctx term)]
    (if (= status :ko)
      [:ko {:msg "Qed step failed: cannot infer term type."
            :cause proof-type
            :meta meta}]
      [:ok [def-env term proof-type]])))


(defn elab-print [def-env ctx term meta]
  (println "============================")
  (let [[term' _] (norm/delta-step def-env ctx term)]
    (pp/pprint (unparser/unparse term')))
  (println "============================"))

(defn elab-print-type [def-env ctx term meta]
  (println "============================")
  (let [[status ty _] (typing/type-of-term def-env ctx term)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term for print-type."
                      {:term term})))
    (print "type of: ") (pp/pprint term)
    (pp/pprint (unparser/unparse ty)))
  (println "============================"))

;;{
;; ## Proof elabortation
;;
;; The proof elaborator simply iterates over the proof steps
;; and dispatch to the adequate elaboration function.
;;
;; All the parsing issues are managed by the elaborator. 
;;}

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
    :print
    (let [[term-expr meta] args
          [status-term term] (parse/parse-term def-env term-expr)]
      (if (= status-term :ko)
        [:ko {:msg "Proof failed at print step: cannot parse term expression."
              :term-expr term-expr
              :meta meta
              :cause term}]
        (do (elab-print def-env ctx term meta)
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
  [proof]
  (if (seq proof)
    (do (when (not (seq (first proof)))
          (throw (ex-info "Compilation failed: malformed proof step." {:step (first proof)})))
        (concat 
         (cond
           (string? (first proof))
           (list)
           (= (ffirst proof) :assume)
           (let [[_ meta params & body] (first proof)
                 params (u/zip params)
                 proof-body (compile-proof body)]
             (concat (map (fn [[x ty]]
                            [:declare x ty meta]) params)
                     proof-body
                     (map (fn [[x _]]
                            [:discharge x meta]) (reverse params))))
           (contains? #{:have :qed :print :print-type} (ffirst proof))
           (list (first proof))
           :else
           (throw (ex-info "Compilation failed: unsupported proof step." {:step (first proof)})))
         (compile-proof (rest proof))))
    ;; the end
    (list)))

(defn check-proof
  [def-env ctx thm-name thm-type steps]
  (println "[check proof] " thm-name)
  (let [proof (compile-proof steps)
        [status res] (elab-proof def-env ctx proof)]
    (if (= status :ko)
      [status res]
      (let [[def-env' proof-term proof-type] res]
        (let [[status thm-type'] [:ok thm-type];; was: (typing/rebuild-type def-env' ctx thm-type)
              ]
          (if (= status :ko)
            (throw (ex-info "Cannot rebuild theorem type." {:thm-type thm-type
                                                            :error thm-type'})))
          (if (not (norm/beta-eq? def-env' ctx proof-type thm-type'))
            [:ko {:msg "Theorem type and proof type do not match."
                  :thm-type thm-type'
                  :proof-type proof-type}]
            [:ok [proof-term proof-type]]))))))





