
(ns latte-kernel.typing-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.typing :refer :all]))

(deftest test-beta-reduction
  (is (= (type-of-term {} [] '□)
         '[:ko {:msg "Kind has not type" :term □}])))



