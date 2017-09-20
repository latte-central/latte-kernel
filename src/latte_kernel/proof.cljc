(ns latte-kernel.proof
  "The proof elaborator and checker."
  (:require [latte-kernel.defenv :as defenv]
            [latte-kernel.typing :as typing]
            [latte-kernel.syntax :as stx]
            [latte-kernel.norm :as norm]))

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

(defn elab-declare [def-env ctx v ty meta]
  [:ok [def-env, (cons [v ty] ctx)]])


;;{
;; ## Local definitions
;;
;;}

(defn elab-have [def-env ctx name ty term meta]
  (let [[status, term-type] (typing/type-of-term def-env ctx term)]
    (if (= status :ko)
      [:ko [{:msg "Have step elaboration failed: cannot synthetize term type."
             :have-name name
             :from term-type}, meta]]
      ;; we have the type here
      (let [[status, rec-ty] (if (= ty '_)
                                [:ok ty]
                                (if (not (norm/beta-eq? def-env ctx term-type ty))
                                  [:ko {:msg "Have step elaboration failed: synthetized term type and expected type do not match"
                                        :have-name name
                                        :expected-type ty
                                        :synthetized-type term-type}]
                                  [:ok ty]))]
        (if (= status :ko)
          [:ko [rec-ty, meta]]
          (if (= name '_)
            [:ok [def-env ctx]]
            [:ok [(defenv/register-definition def-env (defenv/->Definition name [] 0 term rec-ty) true) ctx]]))))))


;;{
;; ## Variable discharge
;;
;; This is the most complex kind of proof step, at least if
;; efficiency is a concern (which it is for proof checking)
;;
;;}

(defn local-defs-with-free-occurrence [local-defs discharge-var]
  (reduce (fn [discharge-defs [dname, local-def]]
            (if (contains? (stx/free-vars (:parsed-term local-def)) discharge-var)
              (conj discharge-defs dname)
              discharge-defs)) #{} local-defs))


(defn ref-uses-in-term [t]
  (stx/term-reduce {:ref conj} #{} t))

