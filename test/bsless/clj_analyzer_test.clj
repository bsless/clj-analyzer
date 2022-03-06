(ns bsless.clj-analyzer-test
  (:require
   [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
   [bsless.clj-analyzer :as sut]
   [clojure.test :as t]))

(t/deftest matching-args*
  (let [ast
        (sut/analyze
         '((fn [a b]) 1 2))
        methods (-> ast :fn :methods)]
    (t/is (= (nth methods 0) (sut/matching-args* 2 methods)))
    (t/is (nil? (sut/matching-args* 3 methods))))


  (let [ast
        (sut/analyze
         '((fn ([a]) ([a b])) 1 2))
        methods (-> ast :fn :methods)]
    (t/is (= (nth methods 0) (sut/matching-args* 1 methods)))
    (t/is (= (nth methods 1) (sut/matching-args* 2 methods)))
    (t/is (nil? (sut/matching-args* 3 methods))))

  )

(t/deftest find-matching-method
  (let [ast
        (sut/analyze
         '((fn [a b]) 1 2))
        m (-> ast :fn :methods (nth 0))]
    (t/is (= m (sut/find-matching-method ast))))


  (let [ast
        (sut/analyze
         '((fn ([a]) ([a b])) 1 2))
        m (-> ast :fn :methods (nth 1))]
    (t/is (= m (sut/find-matching-method ast))))

  (let [ast
        (sut/analyze
         '((fn ([a]) ([a b])) 1 2 3))]
    (t/is (nil? (sut/find-matching-method ast))))

  )


(t/deftest beta-reduce
  (let [ast
        (sut/analyze
         '((fn [a b] (+ a b)) 1 2))]
    (t/is
     (= '(let* [a__#0 1
                b__#0 2]
           (clojure.lang.Numbers/add a__#0 b__#0))
        (emit-form
         (sut/beta-reduce ast)
         {:hygienic true})))))

(emit-form
 (sut/simplify*
  (sut/analyze '(let [a 1 b 2] (+ a b)))))
