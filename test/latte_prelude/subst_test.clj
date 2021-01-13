(ns latte-prelude.subst-test
  (:require [clojure.test :refer :all]

            [latte-kernel.presyntax :as pstx :refer [parse-term]]
            [latte-kernel.defenv :as defenv]
            [latte.core :as latte :refer [example assume have qed]]

            [latte-prelude.utils :refer [find-term]]
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

  (is (= (find-term (parse 'x)
                    (parse '(lambda [y T] x)))
         [2]))

  ;; XXX: the following is strange, because there's a name
  ;; capture, however we'll progress one step at a time
  (is (= (find-term (parse 'x)
                    (parse '(lambda [x T] x)))
         [2]))
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
           


