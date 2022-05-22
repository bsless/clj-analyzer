(ns bsless.clj-analyzer.passes.beta-reduce
  (:require
   [bsless.clj-analyzer.util :refer [find-first]]))

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

(defn some-first
  [pred coll]
  (transduce
   (keep #(when (pred %) %))
   (completing (fn rf [_acc x] (reduced x)))
   nil
   coll))

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
  [{-fn :fn op :op :as ast}]
  (if (and (= :invoke op) -fn (= :fn (:op -fn)))
    (-invoke->let ast)
    ast))
