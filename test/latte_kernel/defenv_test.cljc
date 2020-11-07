(ns latte-kernel.defenv-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.presyntax :as parse]
            [latte-kernel.defenv :refer :all]))

(deftest test-register-definition
  (is (= (register-definition empty-env (->Definition 'test [] 0 (second (parse/parse-term empty-env '(lambda [x :type] x))) #{} nil {}))
         '[{test #latte_kernel.defenv.Definition{:name test, :params [], :arity 0, :parsed-term (λ [x ✳] x), :term-free-vars #{}, :type nil, :opts {}}} {}])))


(deftest test-fetch-definition
  (is (= (fetch-definition (register-definition empty-env (->Definition 'test [] 0 (second (parse/parse-term empty-env '(lambda [x :type] x))) #{} nil {}))
                           'test)
         '[:ok #latte_kernel.defenv.Definition{:name test, :params [], :arity 0, :parsed-term (λ [x ✳] x), :term-free-vars #{}, :type nil, :opts {}}])))
