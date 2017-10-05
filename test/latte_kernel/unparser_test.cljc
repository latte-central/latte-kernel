
(ns latte-kernel.unparser-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.unparser :refer :all]
            [latte-kernel.syntax :as stx]
            [latte-kernel.presyntax :as parse]
            [latte-kernel.defenv :as defenv]))

(deftest test-prod-impl-unparser
  (is (= (prod-impl-unparser (second (parse/parse-term defenv/empty-env '(==> A B))))
         '[(==> A B) true])))






