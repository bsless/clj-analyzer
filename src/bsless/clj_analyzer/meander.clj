(ns bsless.clj-analyzer.meander
  (:require
   [meander.epsilon :as m]
   [meander.strategy.epsilon :as r]
   [clojure.tools.analyzer.jvm :as ana]
   [clojure.tools.analyzer.ast :as ast]
   [clojure.tools.analyzer.ast.query :as q]
   [clojure.tools.analyzer.passes.emit-form :as e]
   [clojure.edn :as edn]
   [clojure.java.io :as io]
   [bsless.clj-analyzer.util :refer [find-first]]
   ))



(m/defsyntax symbolo [s]
  (if (m/match-syntax? &env)
    `(m/and ~s (m/guard (symbol? ~s)))
    &form))

(m/defsyntax arg-bindo
  [form name index variadic]
  `{:op :binding
    :form (symbolo ~form)
    :name (symbolo ~name)
    :local :arg
    :arg-id (m/and ~index (m/guard (int? ~index)))
    :variadic? (m/and ~variadic (m/guard (boolean? ~variadic)))
    :children []})

(def ^:dynamic *patterns*
  (quote
   {%arg-binding
    {:op :binding
     :form (m/and ?form (m/guard (symbol? ?form)))
     :name (m/and ?name (m/guard (symbol? ?name)))
     :local :arg
     :arg-id (m/and ?index (m/guard (int? ?index)))
     :variadic? (m/and ?variadic (m/guard (boolean? ?variadic)))
     :children []}

    %init-binding
    {:op :binding
     :form (m/and ?form (m/guard (symbol? ?form)))
     :name (m/and ?name (m/guard (symbol? ?name)))
     :local (m/or :let :letfn :loop)
     :init %ast
     :children [:init]}

    %-binding
    {:op :binding
     :form (m/and ?form (m/guard (symbol? ?form)))
     :name (m/and ?name (m/guard (symbol? ?name)))
     :local (m/or :catch :fn :field :this)
     :arg-id (m/and ?index (m/guard (int? ?index)))
     :children []}

    %binding (m/or %arg-binding %init-binding %-binding)

    %case
    {:op :case
     :form (case* ?expr ?shift ?mask ?default ?case-map ?switch-type ?test-type ?skip-check)
     :test %ast
     :tests [%case-test ...]
     :thens [%case-then ...]
     :default %ast
     :switch-type (m/or :sparse :compact)
     :test-type (m/or :int :hash-equiv :hash-identity)
     :skip-check? #{& ?skip-ints}
     :children [:test :tests :thens :default]}

    }
   ))
(comment

  (def node
    (first
     (filterv
      (fn [node] (= :invoke (:op node)))
      (ast/nodes ast))))

  ;;; Beta reduce non-variadic

  (m/rewrite
   node
   {:op :invoke
    :args [!args ..?n]
    :fn {:op :fn
         :methods
         [{:fixed-arity ?n
           :variadic? false
           :params
           [{:op :binding
             :local :arg
             :name !name
             :atom !atom} ...]
           :body ?body}
          ..1]}} ;; there can be only one!
   {:op :let
    :children [:bindings :body]
    :bindings
    [{:op :binding
      :local :let
      :name !name
      :atom !atom
      :init !args
      :children [:init]} ...]
    :body ?body}))

(comment

  (def const-binding
    (ana/analyze
     '(let [a 1 b 2] (+ a b))))

  (defn -inline
    [name expr body]
    (let [s (r/top-down (r/match ~name expr ?x ?x))]
      (s body)))

  ((r/top-down (r/rewrite a 1))
   '(+ a b))

  ((r/top-down
    (r/match
      a 1
      ?x ?x))
   '(+ a b))

  (m/rewrite
    '(+ a b)

    (& !x ..!n ...) [!x !n])

  (m/rewrite '(+ a b)
    (& ?xs) ?xs
    a 1)

  (-inline 'a 1 '(+ a b))

  (defn inline
    [name expr body]
    (let [s (r/top-down
             (r/match
               {:op :local :name ~name} expr
               ?x ?x))]
      (s body)))

  (clojure.tools.analyzer.passes.jvm.emit-form/emit-form
   (m/rewrite
     const-binding

     {:op :let
      :children [:bindings :body]
      :bindings [{:children [:init]
                  :init {:op :const
                         :literal? true
                         :val ?val
                         :type ?type
                         :as ?node}
                  :op :binding
                  :name ?name} & ?bindings]
      :body ?body}

     {:op :let
      :children [:bindings :body]
      :bindings [& (m/app inline ?name ?node ?bindings)]
      :body (m/app inline ?name ?node ?body)})
   {:hygienic true})

  )
