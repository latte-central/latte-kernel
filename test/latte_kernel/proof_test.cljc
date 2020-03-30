(ns latte-kernel.proof-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.presyntax :as parse]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.proof :refer :all]))

(def ctx1 (let [[_ [_ ctx1]] (elab-declare defenv/empty-env [] [] {} 'A '✳ {})]
            ctx1))

(def vdeps1 (let [[_ [_ _ vdeps1]] (elab-declare defenv/empty-env [] [] {} 'A '✳ {})]
             vdeps1))

(def ctx2 (let [[_ [_ ctx2]] (elab-declare defenv/empty-env ctx1 vdeps1 {} 'B '✳ {})]
            ctx2))

(def vdeps2 (let [[_ [_ _ vdeps2]] (elab-declare defenv/empty-env ctx1 vdeps1 {} 'B '✳ {})]
              vdeps2))

(def ctx3 (let [[_ [_ ctx3]] (elab-declare defenv/empty-env ctx2 vdeps2 {}
                                           'f (second (parse/parse-term defenv/empty-env '(==> A B))) {})]
            ctx3))

(def vdeps3 (let [[_ [_ _ vdeps3]] (elab-declare defenv/empty-env ctx2 vdeps2 {}
                                           'f (second (parse/parse-term defenv/empty-env '(==> A B))) {})]
             vdeps3))

(def ctx4 (let [[_ [_ ctx4]] (elab-declare defenv/empty-env ctx3 vdeps3 {} 'x 'A {})]
            ctx4))

(def vdeps4 (let [[_ [_ _ vdeps4]] (elab-declare defenv/empty-env ctx3 vdeps3 {} 'x 'A {})]
              vdeps4))

(deftest test-elab-declare
  ;; Step 0:
  ;; local-defs={}   ctx=[]    var-deps=[]    def-uses={}

  (is (= (elab-declare defenv/empty-env [] [] {} 'A '✳ {})
         '[:ok [[{} {}] ([A ✳]) ([A #{}]) {}]]))

  ;; Step 1: [:declare A *]
  ;; local-defs={}   ctx=[[A *]]   var-deps=[[A #{}]]    def-uses={}

  (is (= ctx1 '([A ✳])))

  (is (= vdeps1 '([A #{}])))

  ;; Step 2: [:declare B *]
  ;; local-defs={}   ctx=[[B *] [A *]]   var-deps=[[B #{}] [A #{}]]    def-uses={}
  (is (= ctx2 '([B ✳] [A ✳])))
  (is (= vdeps2 '([B #{}] [A #{}])))

  ;; Step 3: [:declare f (==> A B)]
  ;; local-defs={}   ctx=[[f (==> A B)] [B *] [A *]]   var-deps=[[f #{}][B #{}] [A #{}]]  def-uses={}
  (is (= ctx3 '([f (Π [⇧ A] B)] [B ✳] [A ✳])))
  (is (= vdeps3 '([f #{}] [B #{}] [A #{}])))

  ;; Step 4: [:declare x A]
  ;; local-defs={}   ctx=[[x A] [f (==> A B)] [B *] [A *]]   var-deps=[[x #{}][f #{}][B #{}] [A #{}]]  def-uses={}
  (is (= ctx4 '([x A] [f (Π [⇧ A] B)] [B ✳] [A ✳])))
  (is (= vdeps4 '([x #{}] [f #{}] [B #{}] [A #{}]))))


(deftest test-update-var-deps
  (is (= (update-var-deps vdeps4 '<a> 'f)
         '[[x #{<a>}] [f #{<a>}] [B #{<a>}] [A #{<a>}]]))

  (is (= (-> vdeps4
             (update-var-deps '<a> 'f)
             (update-var-deps '<a> (second (parse/parse-term defenv/empty-env '(==> A B)))))
         '[[x #{<a>}] [f #{<a>}] [B #{<a>}] [A #{<a>}]])))



(let [state5 (second (elab-have defenv/empty-env ctx4 vdeps4 {} '<a> (second (parse/parse-term defenv/empty-env '(==> A B))) 'f {}))
      [def-env5 ctx5 vdeps5 dfuses5] state5]
  (def def-env5 def-env5)
  (def ctx5 ctx5)
  (def vdeps5 vdeps5)
  (def dfuses5 dfuses5))

(let [state6 (second (elab-have def-env5 ctx5 vdeps5 dfuses5 '<b> 'B (second (parse/parse-term def-env5 '(<a> x))) {}))
      [def-env6 ctx6 vdeps6 dfuses6] state6]
  (def def-env6 def-env6)
  (def ctx6 ctx6)
  (def vdeps6 vdeps6)
  (def dfuses6 dfuses6))

(deftest test-ref-uses-in-term
  (is (= (ref-uses-in-term (:parsed-term (second (defenv/fetch-definition def-env6 '<a>))))
         #{}))

  (is (= (ref-uses-in-term (:parsed-term (second (defenv/fetch-definition def-env6 '<b>))))
         '#{<a>})))

(deftest test-update-def-uses
  (is (= (update-def-uses dfuses5 '<b> (:parsed-term (second (defenv/fetch-definition def-env6 '<b>))))
         '{<a> #{<b>}})))

(deftest test-elab-have
  ;; Step 5 : [:have <a> (==> A B) f]
  ;; local-defs={<a>:=f::(==> A B)}
  ;; ctx=[[x A] [f (==> A B)] [B *] [A *]]
  ;; var-deps=[[x #{}][f #{<a>}][B #{<a>}] [A #{<a>}]]  def-uses={<a> #{}}

  (is (= ctx5 ctx4))

  (is (defenv/registered-definition? def-env5 '<a>))

  (is (= (second(defenv/fetch-definition def-env5 '<a> true))
         '#latte_kernel.defenv.Definition{:name <a>, :params [], :arity 0, :parsed-term f, :type (Π [⇧ A] B), :opts {}}))

  (is (= vdeps5
         '[[x #{<a>}] [f #{<a>}] [B #{<a>}] [A #{<a>}]]))

  (is (= dfuses5
         '{<a> #{}}))

  ;; Step 6 : [:have <b> B (<a> x)]
  ;; local-defs={<a>:=f::(==> A B)
  ;;             <b>:=(<a> x)::B}
  ;; ctx=[[x A] [f (==> A B)] [B *] [A *]]
  ;; var-deps=[[x #{<b>}][f #{<a>}][B #{<a>,<b>}] [A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}
  (is (= ctx6 ctx5))

  (is (defenv/registered-definition? def-env6 '<a>))
  (is (defenv/registered-definition? def-env6 '<b>))

  (is (= (second(defenv/fetch-definition def-env6 '<b> true))
         '#latte_kernel.defenv.Definition{:name <b>, :params [], :arity 0, :parsed-term [(<a>) x], :type B, :opts {}}))

  (is (= vdeps6
         '[[x #{<a> <b>}] [f #{<a> <b>}] [B #{<a> <b>}] [A #{<a> <b>}]]))

  (is (= dfuses6
         '{<a> #{<b>}, <b> #{}})))




(deftest test-abstract-local-defs
  (is (= (:params (second (defenv/fetch-definition (abstract-local-def def-env6 '<b> 'x 'A) '<b>)))
         '[[x A]])))

(deftest test-gen-local-calls
  (is (= (gen-local-calls (second (parse/parse-term def-env5 '[(<a>) x])) '#{<a>} 'f)
         '[(<a> f) x])))


(let [state7 (elab-discharge def-env6 ctx6 vdeps6 dfuses6 'x {})
      [def-env7 ctx7 vdeps7 dfuses7] state7]
  (def def-env7 def-env7)
  (def ctx7 ctx7)
  (def vdeps7 vdeps7)
  (def dfuses7 dfuses7))

(let [state8 (elab-discharge def-env7 ctx7 vdeps7 dfuses7 'f {})
      [def-env8 ctx8 vdeps8 dfuses8] state8]
  (def def-env8 def-env8)
  (def ctx8 ctx8)
  (def vdeps8 vdeps8)
  (def dfuses8 dfuses8))

(let [state9 (elab-discharge def-env8 ctx8 vdeps8 dfuses8 'B {})
      [def-env9 ctx9 vdeps9 dfuses9] state9]
  (def def-env9 def-env9)
  (def ctx9 ctx9)
  (def vdeps9 vdeps9)
  (def dfuses9 dfuses9))

(let [state10 (elab-discharge def-env9 ctx9 vdeps9 dfuses9 'A {})
      [def-env10 ctx10 vdeps10 dfuses10] state10]
  (def def-env10 def-env10)
  (def ctx10 ctx10)
  (def vdeps10 vdeps10)
  (def dfuses10 dfuses10))

(deftest test-elab-discharge
  ;; Step 7 : [:discharge x]
  ;; local-defs={<a>:=f::(==> A B)
  ;;             <b>(x::A):=(<a> x)::B}
  ;; ctx=[[f (==> A B)] [B *] [A *]]
  ;; var-deps=[[f #{<a>}][B #{<a>,<b>}] [A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}
  (is (= ctx7
         '([f (Π [⇧ A] B)] [B ✳] [A ✳])))

  (is (= (second (defenv/fetch-definition def-env7 '<a> true))
         '#latte_kernel.defenv.Definition{:name <a>, :params [[x A]], :arity 1, :parsed-term f, :type (Π [⇧ A] B), :opts {}}))

  (is (= (second (defenv/fetch-definition def-env7 '<b> true))
         '#latte_kernel.defenv.Definition{:name <b>, :params [[x A]], :arity 1, :parsed-term [(<a> x) x], :type B, :opts {}}))

  (is (= vdeps7
         '([f #{<a> <b>}] [B #{<a> <b>}] [A #{<a> <b>}])))

  (is (= dfuses7
         '{<a> #{<b>}, <b> #{}}))


  ;; Step 8 : [:discharge f]
  ;; local-defs={<a>(f::(==> A B)):=f::(==> (==> A B) (==> A B))
  ;;             <b>(f::(==> A B), x::A):=((<a> f) x)::B}
  ;; ctx=[[B *] [A *]]
  ;; var-deps=[[B #{<a>,<b>}] [A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}
  (is (= ctx8
         '([B ✳] [A ✳])))

  (is (= (second (defenv/fetch-definition def-env8 '<a> true))
         '#latte_kernel.defenv.Definition{:name <a>, :params [[f (Π [⇧ A] B)] [x A]], :arity 2, :parsed-term f, :type (Π [⇧ A] B), :opts {}}))

  (is (= (second (defenv/fetch-definition def-env8 '<b> true))
         '#latte_kernel.defenv.Definition{:name <b>, :params [[f (Π [⇧ A] B)] [x A]], :arity 2, :parsed-term [(<a> f x) x], :type B, :opts {}}))

  (is (= vdeps8
         '([B #{<a> <b>}] [A #{<a> <b>}])))

  (is (= dfuses8
         '{<a> #{<b>}, <b> #{}}))


  ;; Step 9 : [:discharge B]
  ;; local-defs={<a>(B::*, f::(==> A B)):=f::(forall [B *] (==> (==> A B) (==> A B)))
  ;;             <b>(B::*, f::(==> A B), x::A):=(forall [B *] ((<a> B f) x))::(==> B B)}
  ;; ctx=[A *]]
  ;; var-deps=[[A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}
  (is (= ctx9
         '([A ✳])))

  (is (= (second (defenv/fetch-definition def-env9 '<a> true))
         '#latte_kernel.defenv.Definition{:name <a>, :params [[B ✳] [f (Π [⇧ A] B)] [x A]], :arity 3, :parsed-term f, :type (Π [⇧ A] B), :opts {}}))

  (is (= (second (defenv/fetch-definition def-env9 '<b> true))
         '#latte_kernel.defenv.Definition{:name <b>, :params [[B ✳] [f (Π [⇧ A] B)] [x A]], :arity 3, :parsed-term [(<a> B f x) x], :type B, :opts {}}))

  (is (= vdeps9
         '([A #{<a> <b>}])))

  (is (= dfuses9
         '{<a> #{<b>}, <b> #{}}))

  ;; Step 10 : [:discharge A]
  ;; local-defs={<a>(A::*, B::*, f::(==> A B)):=f::(forall [A B *] (==> (==> A B) (==> A B)))
  ;;             <b>(A::*, B::*, f::(==> A B), x::A):=(forall [A B *] ((<a> A B f) x))::(==> B B)}
  ;; ctx=[A *]]
  ;; var-deps=[[A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}
  (is (= ctx10
         '()))

  (is (= (second (defenv/fetch-definition def-env10 '<a> true))
         '#latte_kernel.defenv.Definition{:name <a>, :params [[A ✳] [B ✳] [f (Π [⇧ A] B)] [x A]], :arity 4, :parsed-term f, :type (Π [⇧ A] B), :opts {}}))

  (is (= (second (defenv/fetch-definition def-env10 '<b> true))
         '#latte_kernel.defenv.Definition{:name <b>, :params [[A ✳] [B ✳] [f (Π [⇧ A] B)] [x A]], :arity 4, :parsed-term [(<a> A B f x) x], :type B, :opts {}}))

  (is (= vdeps10
         '()))

  (is (= dfuses10
         '{<a> #{<b>}, <b> #{}})))




(deftest test-elab-qed

  ;; Step 11 :
  ;; [:qed <a> (forall [A B *] (==> (==> A B) (==> A B)))]

  (is (= (elab-qed def-env10 ctx10 '(<a>) {})
         '[:ok [[{} {<a> #latte_kernel.defenv.Definition{:name <a>, :params [[A ✳] [B ✳] [f (Π [⇧ A] B)] [x A]], :arity 4, :parsed-term f, :type (Π [⇧ A] B), :opts {}}, <b> #latte_kernel.defenv.Definition{:name <b>, :params [[A ✳] [B ✳] [f (Π [⇧ A] B)] [x A]], :arity 4, :parsed-term [(<a> A B f x) x], :type B, :opts {}}}] (<a>) (Π [A ✳] (Π [B ✳] (Π [f (Π [⇧ A] B)] (Π [x A] (Π [⇧ A] B)))))]])))


(deftest test-elab-proof
  (is (= (elab-proof defenv/empty-env []
                     '[[:declare A :type {}]
                       [:declare B :type {}]
                       [:declare f (==> A B) {}]
                       [:declare x A {}]
                       [:have <a> (==> A B) f {}]
                       [:have <b> B (<a> x) {}]
                       [:discharge x {}]
                       [:discharge f {}]
                       [:discharge B {}]
                       [:discharge A {}]
                       [:qed <a> {}]])
         '[:ok [[{} {<a> #latte_kernel.defenv.Definition{:name <a>, :params [[A ✳] [B ✳] [f (Π [⇧ A] B)] [x A]], :arity 4, :parsed-term f, :type (Π [⇧ A] B), :opts {}}, <b> #latte_kernel.defenv.Definition{:name <b>, :params [[A ✳] [B ✳] [f (Π [⇧ A] B)] [x A]], :arity 4, :parsed-term [(<a> A B f x) x], :type B, :opts {}}}] (<a>) (Π [A ✳] (Π [B ✳] (Π [f (Π [⇧ A] B)] (Π [x A] (Π [⇧ A] B)))))]])))

(deftest test-compile-proof
  (is (= (compile-proof '[[:assume {:line 1}
                           [A :type
                            B :type
                            f (==> A B)
                            x A]
                           [:have <a> (==> A B) f {:line 2}]
                           [:have <b> B (<a> x) {:line 3}]]
                          [:qed <a> {:line 4}]])

         '([:declare A :type {:line 1}]
           [:declare B :type {:line 1}]
           [:declare f (==> A B) {:line 1}]
           [:declare x A {:line 1}]
           [:have <a> (==> A B) f {:line 2}]
           [:have <b> B (<a> x) {:line 3}]
           [:discharge x {:line 1}]
           [:discharge f {:line 1}]
           [:discharge B {:line 1}]
           [:discharge A {:line 1}]
           [:qed <a> {:line 4}])))

  (is (= (compile-proof '[:type :type (==> A B)]
                        '[[:assume {:line 1}
                           [A _
                            B _
                            f _
                            x A]
                           [:have <a> (==> A B) f {:line 2}]
                           [:have <b> B (<a> x) {:line 3}]]
                          [:qed <a> {:line 4}]])

         '([:declare A :type {:line 1}]
           [:declare B :type {:line 1}]
           [:declare f (==> A B) {:line 1}]
           [:declare x A {:line 1}]
           [:have <a> (==> A B) f {:line 2}]
           [:have <b> B (<a> x) {:line 3}]
           [:discharge x {:line 1}]
           [:discharge f {:line 1}]
           [:discharge B {:line 1}]
           [:discharge A {:line 1}]
           [:qed <a> {:line 4}]))))



(deftest test-proof
  (is (= (elab-proof defenv/empty-env []
                    (compile-proof '[[:assume {:line 1}
                                      [A :type
                                       B :type
                                       f (==> A B)
                                       x A]
                                      [:have <a> (==> A B) f {:line 2}]
                                      [:have <b> B (<a> x) {:line 3}]]
                                     [:qed <a> {:line 4}]]))
         '[:ok [[{} {<a> #latte_kernel.defenv.Definition{:name <a>, :params [[A ✳] [B ✳] [f (Π [⇧ A] B)] [x A]], :arity 4, :parsed-term f, :type (Π [⇧ A] B), :opts {}}, <b> #latte_kernel.defenv.Definition{:name <b>, :params [[A ✳] [B ✳] [f (Π [⇧ A] B)] [x A]], :arity 4, :parsed-term [(<a> A B f x) x], :type B, :opts {}}}] (<a>) (Π [A ✳] (Π [B ✳] (Π [f (Π [⇧ A] B)] (Π [x A] (Π [⇧ A] B)))))]]))

  (is (= (check-proof defenv/empty-env [] 'my-thm
                      (second (parse/parse-term defenv/empty-env '(forall [A B :type] (==> (==> A B) (==> A A B)))))
                      '[[:assume {:line 1}
                         [A :type
                          B :type
                          f (==> A B)
                          x A]
                         [:have <a> (==> A B) f {:line 2}]
                         [:have <b> B (<a> x) {:line 3}]]
                        [:qed <a> {:line 4}]])
         '[:ok [(<a>) (Π [A ✳] (Π [B ✳] (Π [f (Π [⇧ A] B)] (Π [x A] (Π [⇧ A] B)))))]])))
