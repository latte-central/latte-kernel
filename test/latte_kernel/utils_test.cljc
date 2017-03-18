(ns latte-kernel.utils-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.utils :refer :all]))

(deftest test-vconcat
  (is (= (vconcat [1 2 3] [4 5 6])
         [1 2 3 4 5 6])))

(deftest test-vcons
  (is (= (vcons 1 [2 3 4])
         [1 2 3 4])))

(deftest test-vectorn?

  (is (= (vectorn? [1 2 3 4] 4)
         true))

  (is (= (vectorn? [1 2 3 4 5 6 7 8] 4)
         true))

  (is (= (vectorn? [1 2 3 4 5 6 7] 4)
         false)))


