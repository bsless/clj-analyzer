(ns bsless.clj-analyzer.passes.occurs
  (:require
   [clojure.tools.analyzer.jvm :as ana]
   [clojure.tools.analyzer.ast :as ast]
   #_[clojure.tools.analyzer.ast.query :as q]
   #_[clojure.tools.analyzer.passes.emit-form :as e]
   #_[clojure.tools.analyzer.passes.jvm.emit-form :as jvm.e]
   #_[clojure.edn :as edn]
   #_[clojure.java.io :as io]))

(comment
  (ana/analyze
   '(let [a 1
          b (+ a 2)
          a (+ a b)]
      (+ a (+ a b)))
   (ana/empty-env)
   {:passes-opts (assoc
                  ana/default-passes-opts
                  :uniquify/uniquify-env true)}))

(defn safe?
  [x]
  (or (identical? ::once-safe x)
      (identical? ::multi-safe x)))

(defn unsafe?
  [x]
  (or (identical? ::once-unsafe x)
      (identical? ::multi-unsafe x)))

(defn occurs-safely?
  [ast name]
  (safe? (get (::occurs ast) name)))

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

(defmethod classify-occurs* :if
  [{:keys [test then else]}]
  (occurs+ (::occurs test)
           (occurs* (::occurs then) (::occurs else))))

#_
(defmethod classify-occurs* :case
  [{:keys [test #_tests thens default]}]
  (let [occurs (mapv ::occurs thens)
        _ (some #{::unsafe} occurs)]
    )
  )

#_
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
