
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





