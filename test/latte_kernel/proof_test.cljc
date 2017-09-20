
(ns latte-kernel.proof-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.presyntax :as parse]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.proof :refer :all]))

(def ctx1 (let [[_ [_ ctx1]] (elab-declare defenv/empty-env [] 'A '✳ {})]
            ctx1))

(def ctx2 (let [[_ [_ ctx2]] (elab-declare defenv/empty-env ctx1 'B '✳ {})]
            ctx2))

(def ctx3 (let [[_ [_ ctx3]] (elab-declare defenv/empty-env ctx2 'f (second (parse/parse-term defenv/empty-env '(==> A B))) {})]
            ctx3))

(def ctx4 (let [[_ [_ ctx4]] (elab-declare defenv/empty-env ctx3 'x 'A {})]
            ctx4))

(deftest test-elab-declare
  (is (= (elab-declare defenv/empty-env [] 'A '✳ {})
         '[:ok [[{} {}] ([A ✳])]]))

  (is (= ctx1 '([A ✳])))

  (is (= ctx2 '([B ✳] [A ✳])))

  (is (= ctx3 '([f (Π [⇧ A] B)] [B ✳] [A ✳])))

  (is (= ctx4 '([x A] [f (Π [⇧ A] B)] [B ✳] [A ✳]))))

(def state5 (second (elab-have defenv/empty-env ctx4 '<a> (second (parse/parse-term defenv/empty-env '(==> A B))) 'f {})))

(def state6 (second (elab-have (first state5) (second state5) '<b> 'B (second (parse/parse-term (first state5) '(<a> x))) {})))


(deftest test-elab-have
  (let [[def-env5 ctx5] state5]
    (is (= ctx5 ctx4))

    (is (defenv/registered-definition? def-env5 '<a>))

    (is (= (second(defenv/fetch-definition def-env5 '<a> true))
           '#latte_kernel.defenv.Definition{:name <a>, :params [], :arity 0, :parsed-term f, :type (Π [⇧ A] B)})))

  (let [[def-env6 ctx6] state6]
    (is (= ctx6 ctx4))

    (is (defenv/registered-definition? def-env6 '<a>))
    (is (defenv/registered-definition? def-env6 '<b>))

    (is (= (second(defenv/fetch-definition def-env6 '<b> true))
           '#latte_kernel.defenv.Definition{:name <b>, :params [], :arity 0, :parsed-term [(<a>) x], :type B}))))

(deftest test-local-defs-with-free-occurrence
  (is (= (local-defs-with-free-occurrence (second (first state6)) 'x)
         #{'<b>})))

