(ns bsless.clj-analyzer
  (:require
   [meander.epsilon :as m]
   [meander.strategy.epsilon :as r]
   [clojure.tools.analyzer.jvm :as ana]
   [clojure.tools.analyzer.ast :as ast]
   [clojure.tools.analyzer.ast.query :as q]
   [clojure.tools.analyzer.passes.emit-form :as e]
   [clojure.edn :as edn]
   [clojure.java.io :as io]
   ))

(defn- download-ast-ref!
  []
  (->> "https://raw.githubusercontent.com/clojure/tools.analyzer.jvm/master/spec/ast-ref.edn"
       slurp
       (spit "ast-ref.edn")))

(defn load-ast-ref!
  []
  (with-open [r (io/reader "ast-ref.edn")]
    (edn/read (java.io.PushbackReader. r))))

(comment
  (def ast-ref (load-ast-ref!)))

(comment
  (def the-core (clojure.tools.analyzer.jvm/analyze-ns 'clojure.core)))

(comment
  (ast/ast->eav
   (ana/analyze
    '(defn foo [m a b] (get-in m [a b])))))

(comment
  (ast/ast->eav
   (ana/analyze
    '(defn foo
       [m a b]
       ((fn [m ks] (reduce get m ks)) m [a b])))))

(comment
  (def ast
    (ana/analyze
     '(defn foo
        [m a b]
        ((fn [m ks] (reduce get m ks)) m [a b])))))


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
  (ana/analyze
   '(let [a 1 b 2] (+ a b))))

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

(defn some-first
  [pred coll]
  (transduce
   (keep #(when (pred %) %))
   (completing (fn rf [acc x] (reduced x)))
   nil
   coll))

(comment
  (ana/analyze
   '(defn foo [x & y] (apply + x y))))

(defn- -find-matching-method
  [^long argc methods]
  (or
   (some-first #(== argc (:fixed-arity %)) methods)
   (some-first (every-pred :variadic? #(<= (:fixed-arity %) argc)) methods)))

(defn- params+args
  [params args]
  (mapv
   (fn [param arg]
     (->
      param
      (dissoc :arg-id :variadic?)
      (assoc :local :let
             :init arg
             :children [:init])))
   params
   args))

(defn- -invoke->let
  [{-fn :fn :as ast}]
  (let [{:keys [args]} ast
        argc (count args)
        methods (:methods -fn)
        method (-find-matching-method argc methods)]
    (when-not method
      (throw (ex-info "No matching arity found" ast)))
    (let [params (:params method)
          bindings (params+args params args)]
      (->
       method
       (dissoc :params)
       (assoc :children [:bindings :body]
              :op :let
              :bindings bindings)))))

(defn invoke->let
  "First half of beta reduction"
  {:pass-info
   {:walk :post
    :depends [#'clojure.tools.analyzer.passes.jvm.validate-loop-locals/validate-loop-locals]}}
  [{-fn :fn op :op :as ast}]
  (if (and (= :invoke op) -fn (= :fn (:op -fn)))
    (-invoke->let ast)
    ast))

(let [sentinel (Object.)]
  (defn- sum-maps
    ([] {})
    ([m] m)
    ([m1 m2]
     (reduce-kv
      (fn [m k v]
        (let [v' (m1 k sentinel)]
          (assoc m k (if (.equals sentinel v') v (+ v' v)))))
      m1
      m2))))

(defn -occurs
  "Counts occurrences of local names."
  [{:keys [op name children] :as ast}]
  (assoc
   ast
   ::occurs
   (case op
     :local {name 1}
     (transduce
      (keep ::occurs)
      sum-maps
      {}
      (ast/children ast)))))

(def default-passes-opts
  (assoc
   ana/default-passes-opts
   :uniquify/uniquify-env true))

(comment
  (ast/postwalk
   (ana/analyze
    '(let [a 1
           b (+ a 2)]
       (+ a (+ a b)))
    (ana/empty-env)
    {:passes-opts default-passes-opts})
   -occurs))

(defn -update-env-with-names
  [ast]
  (update-in ast [:env :locals] #(reduce-kv (fn [m k v] (assoc m (:name v) v)) % %)))

(comment
  (ast/postwalk
   (ana/analyze
    '(let [a 1
           b (+ a 2)]
       (+ a (+ a b)))
    (ana/empty-env)
    {:passes-opts default-passes-opts})
   (comp -update-env-with-names -occurs)))

(defmulti classify-occurs* :op)

(defmethod classify-occurs* :fn
  [{:keys [op name children env] :as ast}]
  (let [occurs (::occurs ast)
        ranking (::ranking ast)
        locals (:locals env)]
    (reduce-kv
     (fn [m k v]
       (if-let [e (locals k)]
         (assoc m k ::unsafe)
         m))
     {}
     occurs)))

#_
(defn -classify-occurs
  [{:keys [op name children env]}]
  (let [occurs (::occurs ast)
        ranking (::ranking ast)
        locals (:locals env)]
    (case op
      :fn (reduce-kv (fn [m k v] (if-let [e (locals k)]
                                  (assoc m k ::unsafe)
                                  m)) {} occurs))))


(defn -copy-prop
  [{:keys [op bindings body] :as ast}]
  (if (= :let op)
    (into
     {}
     (map
      (fn [{:keys [init] :as binding}]
        (when (and (= :local (:op init))
                   (= 1 (get (::occurs ast) (:name init))))
          [(:name binding) (:name init)])))
     bindings)
    ast))

(comment
  (clojure.tools.analyzer.passes/schedule ana/default-passes {:debug? true})

  (def run-passes
    (clojure.tools.analyzer.passes/schedule (conj ana/default-passes #'invoke->let) #_{:debug? true}))

  (binding [ana/run-passes run-passes]
    (ana/analyze
     '(defn foo
        [m a b]
        ((fn [m ks] (reduce get m ks)) m [a b]))))

  (ast/postwalk ast invoke->let)
  (ana/run-passes
   (ast/postwalk ast invoke->let))
  (e/emit-bindings)
  (ast/cycling )
  (def ast2
    (ana/analyze
     (e/emit-form
      (ast/postwalk ast invoke->let)
      {:hygienic true})))

  (ast/postwalk ast2 -occurs))

(comment
  (q/unfold-expression-clauses
   '{:where [[(inc (dec ?foo)) ?bar] ] }))

(defmacro definline+
  "Like [[definline]] but takes multiple arities form.
  Cannot be used with `&` but supports multiple arities."
  {:added "1.0"}
  [name & decls]
  (let [[pre-args decls] (split-with (comp not list?) decls)
        argvs (map first decls)
        body' (eval (list* `fn (symbol (str "apply-inline-" name)) decls))
        decls' (map (fn build-decls [argv] (list argv (apply body' argv))) argvs)]
    `(do
       (defn ~name ~@pre-args ~@decls')
       (alter-meta! (var ~name) assoc :inline (fn ~name ~@decls) :inline-arities ~(into #{} (map count) argvs))
       (var ~name))))

(comment
  (definline+ foo
    ([a b] `(+ ~a ~b))
    ([a b c] `(+ ~a ~b ~c))))

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
