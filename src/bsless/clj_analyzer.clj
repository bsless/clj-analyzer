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

#_
(defn -occurs
  {:state (fn [] (atom {}))}
  [state ast]
  (when (= :local (:op ast))
    (swap! state update (:name ast) (fnil inc 0)))
  (assoc ast ::occurs at))

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
