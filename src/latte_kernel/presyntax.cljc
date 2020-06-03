
(ns latte-kernel.presyntax
  "The rich syntax of the lambda-calculus implemented
  by LaTTe."
  (:require [latte-kernel.defenv :as defenv]))

;;{
;; # The LaTTe language (rich) syntax

;; The internal language of LaTTe is a very simple
;; lambda-calculus. In this namespace is defined
;; the richer external syntax forming the user
;; inputs.

;;}

;;{
;; ## Reserved symbols

;; There are a few symbols that are reserved and thus
;; not usable as variable names, definitions, etc.

;;}

(def +reserved-symbols+
  '#{□ ✳ λ Π ⟶ ∃ ∀ lambda forall exists})

;;{
;; The symbols above are well explained in the
;; book "Type theory and formal proof: an introduction".

;;  - □ (or `:kind`) is a sort, the type of all kinds (Page 87)
;;  - ✳ (or `:type`) is a sort, the type of all types (Page 70)
;;  - λ is the symbol of lambda abstractions (Page 1)
;;  - Π is the symbol of product abstractions (Page 72)
;;  - ⟶ is the arrow type (Page 34)
;;  - ∃ is the existential quantifier (Page 247)
;;  - ∀ is the universal quantifier (Page 246)
;;}

(defn reserved-symbol?
  "Is `s` a reserved symbol?"
  [s] (contains? +reserved-symbols+ s))

(defn kind?
  "Is `t` the sort `:kind`?"
  [t] (contains? '#{:kind □} t))

(defn type?
  "Is `t` the sort `:type`?"
  [t] (contains? '#{:type ✳} t))

;;{
;; ## Main parsing function
;;
;; This is the main parsing function, that
;; dispatches given four subcases depending
;; on the term to parse being:
;;   - the sort `:kind`
;;   - the sort `:type`
;;   - a sequential term, covering all parenthesized expressions
;;   - an isolated symbol
;;}

(declare parse-compound-term
         parse-symbol-term)

(defn parse-term
  "Parses the input term `t` in definitional environment `def-env` and
  set of bound variables `bound`.
  The function returns a pair with the keyword `:ok` and the parsed term if the
  parse was successful, else `:ko` followed by a parse error."
  ([def-env t] (parse-term def-env t #{}))
  ([def-env t bound]
   (cond
     (kind? t) [:ok '□]
     (type? t) [:ok '✳]
     (sequential? t) (parse-compound-term def-env t bound)
     (symbol? t) (parse-symbol-term def-env t bound)
     ;; parse-through by default (for implicit arguments)
     :else [:ok [::host-constant t]])))
;; or a parse error?
;; :else [:ko {:msg "Cannot parse term" :term t}])))

;;{
;; **Remark**: that errors are always returned as a map with
;; at least a key `:msg` for the error message, the other key,value pairs
;; depend on the type of error message.
;;}

;;{
;; The following is the main parsing function in the API.
;;}

(defn parse
  "Parse term `t` in definitional environment `def-env` (empty by default)."
  ([t] (parse defenv/empty-env t))
  ([def-env t] (let [[status t'] (parse-term def-env t)]
                 (if (= status :ko)
                   (throw (ex-info "Parse error" t'))
                   t'))))

;;{
;; ## Symbol parsing
;;
;; A symbol can be either:
;;  - a reserved symbol, in which case an error is returned
;; (it cannot be used at an isolated place)
;;  - an occurrence of a bound variable
;;  - the name of a registered definition of arity 0
;;  - an occurrence of a free variable
;;}

(defn parse-symbol-term
  "Parses the symbol `sym`."
  [def-env sym bound]
  (cond
    (reserved-symbol? sym) [:ko {:msg "Symbol is reserved" :term sym}]
    (contains? bound sym) [:ok sym]
    (defenv/registered-definition? def-env sym) [:ok (list (defenv/qualify-def def-env sym))]
    :else
    ;; free variable
    [:ok sym]))

;;{
;; ## Compound term parsing
;;
;; In LaTTe a compound term may be:
;;   - a lambda abstraction
;;   - a product abstraction
;;   - an arrow type
;;   - an existential
;;   - a defined term, i.e. a "call" to a definition
;;   - an application
;;}

(defn lambda-kw?
  "Lambda abstraction?"
  [t] (or (= t 'λ)
          (= t 'lambda)))

(defn product-kw?
  "Product abstraction?"
  [t]
  (or (= t 'Π)
      (= t '∀)
      (= t 'forall)))

(defn arrow-kw?
  "Arrow type?"
  [t]
  (or (= t '⟶)
      (= t '==>)))

(defn exists-kw?
  "Existential?"
  [t]
  (or (= t '∃)
      (= t 'exists)))

(declare parse-lambda-term
         parse-product-term
         parse-arrow-term
         parse-defined-term
         parse-application-term)

(defn parse-compound-term
  "Parses `t` as a compound term."
  [def-env t bound]
  ;; (println "[parse-compound-term] t=" t)
  (if (empty? t)
    [:ko {:msg "Compound term is empty" :term t}]
    (cond
      (lambda-kw? (first t)) (parse-lambda-term def-env t bound)
      (product-kw? (first t)) (parse-product-term def-env t bound)
      (arrow-kw? (first t)) (parse-arrow-term def-env t bound)
      :else
      (if (and (or (symbol? (first t)) (var? (first t)))
               (defenv/registered-definition? def-env (first t)))
        (let [[status sdef] (defenv/fetch-definition def-env (first t))]
          (cond
            (= status :ko)
            [:ko sdef]
            (not (defenv/latte-definition? sdef))
            (throw (ex-info "Not a LaTTe definition (please report)"
                            {:def sdef}))
            (and (= (:arity sdef) 0)
                 (seq (rest t)))
            (parse-application-term def-env (cons (list (first t)) (rest t)) bound)
            :else
            (parse-defined-term def-env sdef t bound)))
        ;; else
        (parse-application-term def-env t bound)))))

;;{
;; ## Abstractions
;;
;; There are two kinds of abstractions in LaTTe:
;;   - lambda abstractions, i.e. unary unanymous functions of the form `(λ [x t] u)`
;;   - product abstractions, a.k.a. "Pi-types" (also) universal quantifications of the form `(Π [x t] u)`
;;
;; A simple but useful syntactic sugar is proposed:
;;
;; `(λ [x y z t] u)` is the same as `(λ [x t] (λ [y t] (λ [z t] u)))`
;;
;; (and similarly for products).
;;}

(defn parse-binding
  "Parse an abstraction binding form."
  [def-env v bound]
  (cond
    (not (vector? v))
    [:ko {:msg "Binding is not a vector" :term v}]
    (< (count v) 2)
    [:ko {:msg "Binding must have at least 2 elements" :term v}]
    :else
    (let [ty (last v)
          [status ty'] (parse-term def-env ty bound)]
      (if (= status :ko)
        [:ko {:msg "Wrong binding type" :term v :from ty'}]
        (loop [s (butlast v), vars #{}, res []]
          (if (seq s)
            (cond
              (not (symbol? (first s)))
              [:ko {:msg "Binding variable is not a symbol" :term v :var (first s)}]
              (reserved-symbol? (first s))
              [:ko {:msg "Wrong binding variable: symbol is reserved" :term v :symbol (first s)}]
              (contains? vars (first s))
              [:ko {:msg "Duplicate binding variable" :term v :var (first s)}]
              :else (recur (rest s) (conj vars (first s)) (conj res [(first s) ty'])))
            [:ok res]))))))

(defn parse-binder-term
  "Parse the binding vector of an abstraction form."
  [def-env binder t bound]
  (if (< (count t) 3)
    [:ko {:msg (str "Wrong " binder " form (expecting at least 3 arguments)") :term t :nb-args (count t)}]
    (let [[status bindings] (parse-binding def-env (second t) bound)]
      (if (= status :ko)
        [:ko {:msg (str "Wrong bindings in " binder " form") :term t :from bindings}]
        (let [bound' (reduce (fn [res [x _]]
                               (conj res x)) #{} bindings)
              body (if (= (count t) 3)
                     (nth t 2)
                     (rest (rest t)))
              [status body] (parse-term def-env body bound')]
          (if (= status :ko)
            [:ko {:msg (str "Wrong body in " binder " form") :term t :from body}]
            (loop [i (dec (count bindings)), res body]
              (if (>= i 0)
                (recur (dec i) (list binder (bindings i) res))
                [:ok res]))))))))

(defn parse-lambda-term
  "Parse a lambda abstraction."
  [def-env t bound]
  (parse-binder-term def-env 'λ t bound))

(defn parse-product-term
  "Parse a production abstraction."
  [def-env t bound]
  (parse-binder-term def-env 'Π t bound))


;;{
;; ## Arrow types
;;
;; The arrow type `(==> t u)` is the type of functions
;; from values of type `t` to values of type `u`.
;;}

(defn parse-terms
  "Parse a sequence `ts` of terms."
  [def-env ts bound]
  (reduce (fn [res t]
            (let [[status t' :as tres] (parse-term def-env t bound)]
              (if (= status :ok)
                [:ok (conj (second res) t')]
                (reduced tres)))) [:ok []] ts))

(defn parse-arrow-term
  "Parse an arrow type."
  [def-env t bound]
  (if (< (count t) 3)
    [:ko {:msg "Arrow (implies) requires at least 2 arguments"
          :term t
          :nb-args (count (rest t))}]
    (let [[status ts'] (parse-terms def-env (rest t) bound)]
      (if (= status :ko)
        [:ko {:msg "Cannot parse arrow." :term t :from ts'}]
        (loop [ts (rest (reverse ts')), res (last ts')]
          (if (seq ts)
            (recur (rest ts) (list 'Π ['⇧ (first ts)] res))
            [:ok res]))))))


;;{
;; ## Defined terms
;;
;; A defined term references a registered definition.
;; It can be a *notation* in which case it gets expanded
;; or it can be mathematical definition.
;;}

(defn parse-defined-term
  "Parse a defined term."
  [def-env sdef t bound]
  (if (defenv/notation? sdef)
    (let [notation-fn (:notation-fn sdef)
          [status t'] (apply notation-fn (rest t))]
      (if (= status :ko)
        [:ko t']
        (parse-term def-env t' bound)))
    ;; other definitions
    (let [def-name (first t)
          arity (count (rest t))]
      (if (and (get sdef :arity)
               (< (:arity sdef) arity))
        [:ko {:msg "Too many arguments for definition." :term t :def-name def-name :arity arity :nb-args (:arity sdef)}]
        ;; else
        (let [[status ts] (parse-terms def-env (rest t) bound)]
          (if (= status :ko)
            [:ko {:msg "Wrong argument" :term t :from ts}]
            [:ok (list* (defenv/qualify-def def-env def-name) ts)]))))))


;;{
;; ## Applications
;;
;; An application is simply the application of a function to a
;; sequence of arguments, i.e. something of the form `(f e1 e2 ... eN)`.
;;
;; Internally, this will become a set of binary applications, of the form:
;; `[...[[f e1] e2]... eN]`
;;}

(defn left-binarize
  "Binarization (sic!) of an application."
  [t]
  (if (< (count t) 2)
    t
    (loop [s (rest (rest t)), res [(first t) (second t)]]
      (if (seq s)
        (recur (rest s) [res (first s)])
        res))))

(defn parse-application-term
  "Parse an application."
  [def-env t bound]
  ;; (println "[parse-application-term] t=" t)
  (if (< (count t) 2)
    [:ko {:msg "Application needs at least 2 terms" :term t :nb-terms (count t)}]
    (let [[status ts] (parse-terms def-env t bound)]
      ;; (println "   ==> " (left-binarize ts))
      (if (= status :ko)
        [:ko {:msg "Parse error in operand of application" :term t :from ts}]
        [:ok (left-binarize ts)]))))
