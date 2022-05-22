(ns bsless.clj-analyzer
  (:require
   [clojure.tools.analyzer.jvm :as ana]
   [clojure.tools.analyzer.ast :as ast]
   [clojure.edn :as edn]
   [clojure.java.io :as io]))

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

(defn -update-env-with-names
  [ast]
  (update-in ast [:env :locals] #(reduce-kv (fn [m _ v] (assoc m (:name v) v)) % %)))
