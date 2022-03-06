(ns bsless.clj-analyzer.util)

(defn some-rf
  ([] nil)
  ([x] x)
  ([_ x] (if (nil? x) x (reduced x))))

(defn find-first
  [p xs]
  (transduce (filter p) some-rf xs))
