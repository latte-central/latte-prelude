(ns latte-prelude.subst-test
  (:require [clojure.test :refer :all]

            [latte-kernel.presyntax :as pstx :refer [parse-term]]
            [latte-kernel.defenv :as defenv]
            [latte.core :as latte :refer [example assume have qed]]

            [latte-prelude.utils :refer [find-term build-subst-lambda]]
            [latte-prelude.equal :as eq :refer [equal]])
  )

(defn parse
  ([t] (parse {} t))
  ([env t]
   (let [[ok t'] (parse-term (defenv/mkenv env) t)]
     (if (= ok :ok)
       t'
       (throw (ex-info "Parse fail" {:cause t'}))))))

(deftest test-find-term-simple
  (is (= (find-term (parse 'x)
                    (parse 'x))
         [:ok []]))

  (is (= (find-term (parse 'x)
                    (parse 'y))
         [:ko 1]))

  (is (= (find-term (parse 'x)
                    (parse '(lambda [y T] y)))
         [:ko 1]))

  (is (= (find-term (parse 'T)
                    (parse '(lambda [y T] x)))
         [:ok [1]]))

  (is (= (find-term (parse 'x)
                    (parse '(lambda [y T] x)))
         [:ok [2]]))

  ;; A special case, if we are looking for a variable
  ;; that gets bound in the term u (arguably rare case)
  (is (= (find-term (parse 'x)
                    (parse '(lambda [x T] x)))
         [:ko 1]))

  ;; A similar case
  (is (= (find-term (parse 'x)
                    (parse '(lambda [x T] (f x))))
         [:ko 1]))

  (is (= (find-term (parse '(lambda [x T] x))
                    (parse '(lambda [f (==> T T T)] [f (lambda [x T] x)])))
         [:ok [2 1]]))

  (is (= (find-term (parse '(lambda [x T] x))
                    (parse '(lambda [f (==> T T T)] [f (lambda [z T] z)])))
         [:ok [2 1]]))

  (is (= (find-term (parse '(lambda [x T] x))
                    (parse '(lambda [f (==> T T T)] [f (lambda [z T] x)])))
         [:ko 1]))

  (is (= (find-term (parse 'x)
                    (parse (list #'latte-prelude.equal/equal '(f x) '(f x))))
         [:ok [1 1]]))

  (is (= (find-term (parse 'x)
                    (parse (list #'latte-prelude.equal/equal '(f x) '(f x)))
                    2) ;; we ask for the 2-nd occurrence
         [:ok [2 1]]))
     
  )

(deftest test-build-subst-subst-lambda-simple
  (is (= (build-subst-lambda (parse 'x) 'T [] false)
         '(λ [$ T] $)))

  (is (= (build-subst-lambda (parse '(lambda [y T] x)) 'T [1] false)
         '(λ [$ T] (λ [y $] x))))
  
  (is (= (build-subst-lambda (parse '(lambda [y T] x)) 'T [2] false)
         '(λ [$ T] (λ [y T] $))))

  (is (= (build-subst-lambda (parse '(lambda [f (==> T T T)] [f (lambda [x T] x)]))
                             (parse '(==> T T)) [2 1] false)
         '(λ [$ (Π [⇧ T] T)] (λ [f (Π [⇧ T] (Π [⇧ T] T))] [f $]))))
         
  (is (= (build-subst-lambda (parse (list #'latte-prelude.equal/equal '(f x) '(f x))) 'T [1 1] false)
         (list 'λ ['$ 'T] (list #'latte-prelude.equal/equal '[f $] '[f x]))))

  (is (= (build-subst-lambda (parse (list #'latte-prelude.equal/equal '(f x) '(f x))) 'T [2 1] false)
         (list 'λ ['$ 'T] (list #'latte-prelude.equal/equal '[f x] '[f $]))))
  )

;; XXX: why `example` cannot by used in a `deftest`
;; if the full namespace is not given ?
(deftest test-rewrite-simple

  (is (= (example [[T :type] [U :type] [x T] [y T] [f (==> T U)]]
             (==> (equal x y)
                  (equal (f x) (f y)))
           ;; proof
           (assume [Heq _]
             (have <a> _ :by (latte-prelude.equal/eq-subst (lambda [$ T]
                                                                   (latte-prelude.equal/equal (f x) (f $)))
                                                           Heq (latte-prelude.equal/eq-refl (f x)))))
           (qed <a>))
         
         [:checked :example]))
  
  (is (= (example [[T :type] [U :type] [x T] [y T] [f (==> T U)]]
             (==> (equal x y)
                  (equal (f y) (f x)))
           ;; proof
           (assume [Heq _]
             (have <a> _ :by (latte-prelude.equal/rewrite (latte-prelude.equal/eq-refl (f x)) 
                                                          Heq)))
           (qed <a>))
         
         [:checked :example]))

  (is (= (example [[T :type] [U :type] [x T] [y T] [f (==> T U)]]
             (==> (equal x y)
                  (equal (f y) (f x)))
           ;; proof
           (assume [Heq _]
             (have <a> _ :by (latte-prelude.equal/nrewrite 1 (latte-prelude.equal/eq-refl (f x)) 
                                                           Heq)))
           (qed <a>))
         
         [:checked :example]))

  (is (= (example [[T :type] [U :type] [x T] [y T] [f (==> T U)]]
             (==> (equal x y)
                  (equal (f x) (f y)))
           ;; proof
           (assume [Heq _]
             (have <a> _ :by (latte-prelude.equal/nrewrite 2 (latte-prelude.equal/eq-refl (f x)) 
                                                           Heq)))
           (qed <a>))
         
         [:checked :example]))
  )
