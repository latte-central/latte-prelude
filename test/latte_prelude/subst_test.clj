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
         []))

  (is (= (find-term (parse 'x)
                    (parse 'y))
         false))

  (is (= (find-term (parse 'x)
                    (parse '(lambda [y T] y)))
         false))

  (is (= (find-term (parse 'T)
                    (parse '(lambda [y T] x)))
         [1]))

  (is (= (find-term (parse 'x)
                    (parse '(lambda [y T] x)))
         [2]))

  ;; A special case, if we are looking for a variable
  ;; that gets bound in the term u (arguably rare case)
  (is (= (find-term (parse 'x)
                    (parse '(lambda [x T] x)))
         false))

  (is (= (find-term (parse '(lambda [x T] x))
                    (parse '(lambda [f (==> T T T)] [f (lambda [x T] x)])))
         [2 1]))

  (is (= (find-term (parse '(lambda [x T] x))
                    (parse '(lambda [f (==> T T T)] [f (lambda [z T] z)])))
         [2 1]))

  (is (= (find-term (parse '(lambda [x T] x))
                    (parse '(lambda [f (==> T T T)] [f (lambda [z T] x)])))
         false))
     
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
         
  )

;; XXX: why `example` cannot by used in a `deftest` ?
;; (deftest test-subst-ex1

;;   (is (=

;;        (example [[T :type] [U :type] [x T] [y T] [f (==> T U)]]
;;            (==> (equal x y)
;;                 (equal (f x) (f y)))
;;          ;; proof
;;          (assume [Heq _]
;;            (have <a> _ :by (eq/eq-subst (lambda [$ T]
;;                                                 (equal (f x) (f $)))
;;                                         Heq (eq/eq-refl (f x)))))
;;          (qed <a>))

;;        [:checked :example]))
;; )
           


