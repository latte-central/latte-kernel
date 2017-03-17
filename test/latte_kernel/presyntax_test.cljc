
(ns latte-kernel.presyntax-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.presyntax :refer :all]))


(deftest reserved-symbols
  (is (= (reserved-symbol? 'a) false))
  (is (= (reserved-symbol? 'λ) true)))


