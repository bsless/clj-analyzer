(ns bsless.clj-analyzer.passes.inline
  (:require
   [bsless.clj-analyzer.passes.occurs :as occurs]
   [clojure.tools.analyzer.jvm :as ana]
   [clojure.tools.analyzer.ast :as ast]
   [clojure.tools.analyzer.passes.jvm.emit-form :as jvm.e]))

(def ^:private default-passes-opts
  (assoc
   ana/default-passes-opts
   :uniquify/uniquify-env true))

(defn do-inline
  [ast {:keys [name init]}]
  (ast/postwalk
   ast
   (fn [{:keys [op] :as ast}]
     (if (and (= op :local) (= name (:name ast)))
       init
       ast))))

(defn inline
  "Assume AST here is a let-form"
  [{:keys [bindings body] :as ast} binding]
  (let [bindings (remove #(identical? binding %) bindings)]
    (assoc
     ast
     :bindings (mapv #(do-inline % binding) bindings)
     :body (do-inline body binding))))

(comment
  (def ast
    (ast/postwalk
     (ana/analyze
      '(let [a 1
             b (+ a 2)
             a (+ a b)]
         (+ a (+ a b)))
      (ana/empty-env)
      {:passes-opts default-passes-opts})
     occurs/classify))
  (jvm.e/emit-hygienic-form (inline ast (first (:bindings ast)))))

(defn constant?
  [node]
  (= :const (:op node)))

(defn lambda-abstraction?
  [node]
  (= :fn (:op node)))

(defn constructor-application?
  [{:keys [op] :as ast}]
  (and
   (or (= :map op)
       (= :vector op)
       (= :set op)
       (= :new op))
   (every? constant? (ast/children ast))))

(defn whnf?
  "Check if AST node is in Weak Head Normal Form.
  https://wiki.haskell.org/Weak_head_normal_form"
  [node]
  (or (constant? node)
      (lambda-abstraction? node)
      (constructor-application? node)))

(defn inline?
  "Check if a let-binding node can be inlined.
  A binding can be inlined if it is in WHNF or safe to inline."
  [ast {:keys [name init]}]
  (or (whnf? init)
      (occurs/occurs-safely? (get ast name))))
