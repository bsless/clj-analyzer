(ns bsless.clj-analyzer
  (:require
   [clojure.tools.analyzer.jvm :as ana]
   [clojure.tools.analyzer.ast :as ast]
   [clojure.tools.analyzer.ast.query :as q]
   [clojure.tools.analyzer.passes.emit-form :as e]
   [clojure.tools.analyzer.passes.jvm.emit-form :as jvm.e]
   [clojure.edn :as edn]
   [clojure.java.io :as io]
   [bsless.clj-analyzer.util :refer [find-first]]
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

(def default-passes-opts
  (assoc
   ana/default-passes-opts
   :uniquify/uniquify-env true))

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

(defn analyze
  [form]
  (ana/analyze form (ana/empty-env) {:passes-opts default-passes-opts}))

(comment
  (def ast
    (ana/analyze
     '(defn foo
        [m a b]
        ((fn [m ks] (reduce get m ks)) m [a b]))
     (ana/empty-env)
     {:passes-opts default-passes-opts})))

(defn matching-args*
  [n methods]
  (find-first (fn [{:keys [fixed-arity]}] (= n fixed-arity)) methods))

(defn find-matching-method
  [{args :args
    {methods :methods} :fn :as _node}]
  (matching-args* (count args) methods))

(defn ->let-binding
  [name param]
  {:op :binding
   :local :let
   :name name
   :init param
   :children [:init]})

(defn beta-reduce
  [{args :args :as node}]
  (when-let [{:keys [params body]} (find-matching-method node)]
    {:op :let
     :children [:bindings :body]
     :bindings (mapv ->let-binding (mapv :name params) args)
     :body body}))

(defn simplify*
  [{:keys [bindings body] :as node}]
  (let [b (first bindings)]
    (assoc node :body
           (ast/postwalk
            body
            (fn [{:keys [op name] :as node}]
              (if (and (= :local op) (= name (:name b)))
                (:init b)
                node))))))




(comment
  (ana/analyze
   '(let [a 1 b 2] (+ a b))))



(defn some-first
  [pred coll]
  (transduce
   (keep #(when (pred %) %))
   (completing (fn rf [_acc x] (reduced x)))
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

#_(def *-occurs nil)
(defmulti *-occurs vector)
(defmethod *-occurs [:once-safe :once-safe] [_ _] :multi-safe)
(defmethod *-occurs [:multi-safe :once-safe] [_ _] :multi-safe)
(defmethod *-occurs [:once-safe :multi-safe] [_ _] :multi-safe)
(defmethod *-occurs [:multi-safe :multi-safe] [_ _] :multi-safe)

(defmulti occurs :op)

(def inc* (fnil inc 0))

(defmethod occurs :local
  [{{locals :locals #_#_:as env} :env
    #_#_-name :name
    form :form
    :as node}]
  (assoc-in
   node
   [:env :locals form]
   (let [{#_#_local-name :name :as local} (get locals form)]
     (-> local
         (update :occurs-count inc*)
         (assoc :occurs :occurs/once-safe)))))

(comment
  (def local
    {:children [],
     :name 'm__#0,
     :op :local,
     :env
     {:loop-locals 3,
      :locals
      '{m {:form m,
           :name m__#0,
           :variadic? false,
           :op :binding,
           :arg-id 0,
           :local :arg},
        a {:form a,
           :name a__#0,
           :variadic? false,
           :op :binding,
           :arg-id 1,
           :local :arg},
        b {:form b,
           :name b__#0,
           :variadic? false,
           :op :binding,
           :arg-id 2,
           :local :arg}},
      :ns 'bsless.clj-analyzer,
      :loop-id 'loop_21101,
      :once false,
      :context :ctx/expr},
     :o-tag java.lang.Object,
     :variadic? false,
     :arg-id 0,
     :form 'm,
     :tag java.lang.Object,
     :local :arg,
     :assignable? false})
  (occurs local))

(defmethod occurs :if
  [{-test :test
    {{then-locals :locals} :env :as -then} :then
    {{else-locals :locals} :env :as -else} :else
    {locals :locals :as env} :env
    :as node}]
  (reduce-kv
   (fn [m k v]
     (let [{then-count :occurs-count
            then-occurs :occurs
            :as then-local} (get then-locals k)
           {else-count :occurs-count
            else-occurs :occurs
            :as else-local} (get else-locals k)]
       (condp = [then-occurs else-occurs]
         [:occurs/once-safe :occurs/once-safe] :occurs/multi-safe
         [:occurs/multi-safe :occurs/once-safe] :occurs/multi-safe
         [:occurs/multi-safe :occurs/multi-safe] :occurs/multi-safe
         [:occurs/multi-safe :occurs/multi-safe] :occurs/multi-safe
         )
       ))
   locals
   locals))

(comment
  (def ifte (analyze '(let [x 1 y false] (if y (inc x) x)))))

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
           b (+ a 2)
           a (+ a b)]
       (+ a (+ a b)))
    (ana/empty-env)
    {:passes-opts default-passes-opts})
   -update-env-with-names
   #_(comp -update-env-with-names -occurs)))

(defn safe?
  [x]
  (or (identical? ::once-safe x)
      (identical? ::multi-safe x)))

(defn unsafe?
  [x]
  (or (identical? ::once-unsafe x)
      (identical? ::multi-unsafe x)))

;;; Occurrence combinators

(defn -occurs*
  "In branching contexts, occurrence on multiple branches can be safe."
  [x y]
  (cond
    (and (unsafe? x) (unsafe? y)) ::multi-unsafe
    (unsafe? x) x
    (unsafe? y) y
    :else ::multi-safe))

(defn -occurs+
  "In non branching context, every co-occurrence of variable safety is
  multi unsafe."
  [_ _] ::multi-unsafe)

(defn occurs+ [m1 m2] (merge-with -occurs+ m1 m2))
(defn occurs* [m1 m2] (merge-with -occurs* m1 m2))

;;;

(defmulti classify-occurs*
  "Add a map of {name occurrence} for each node in a AST."
  :op)

(defmethod classify-occurs* :local
  [{:keys [name] :as ast}]
  (assoc ast ::occurs {name ::once-safe}))

(defmethod classify-occurs* :default
  [ast]
  (assoc ast ::occurs (reduce occurs+ {} (map ::occurs (ast/children ast)))))

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
     classify-occurs*))
  (jvm.e/emit-hygienic-form (inline ast (first (:bindings ast)))))

(defn constant?
  [node]
  (= :const (:op node)))

(defn lambda-abstraction?
  [node]
  (= :fn (:op node)))

(defn constructor-application?
  [{:keys [op]}]
  (or (= :map op)
      (= :vector op)
      (= :set op)
      (= :new op)))

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
      (safe? (get (::occurs ast) name))))

(defmethod classify-occurs* :if
  [{:keys [test then else]}]
  (occurs+ (::occurs test)
           (occurs* (::occurs then) (::occurs else))))

(defmethod classify-occurs* :case
  [{:keys [test #_tests thens default]}]
  (let [occurs (mapv ::occurs thens)
        _ (some #{::unsafe} occurs)]
    )
  )

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

