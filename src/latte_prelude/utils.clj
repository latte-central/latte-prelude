(ns latte-prelude.utils
  (:require [latte-kernel.syntax :as stx])
)

(defn find-term
  "Finds the `n-th` occurrence of term `t` within term `u` recursively, constructing
  the `path` to the first occurrence. The lookup is simply wrt.
  structural equality."

  ([t u] (find-term t u 1))

  ([t u n-th] (find-term t u [] n-th (stx/free-vars t)))

  ([t u path n-th free]
   (cond
     ;; found an occurrence ?
     (or (= t u) ;; structural equality
         (stx/alpha-eq? t u)  ;; alpha-convertibility
         )
     (if (= n-th 1)
       [:ok path]
       ;; not the seeked occurrence
       [:ko (dec n-th)])

     (stx/binder? u)
     (let [[_ [x ty] body] u]
       (if (free x) ;; cannot equate a bound variable
         [:ko n-th]
         (let [[ok res] (find-term t ty (conj path 1) n-th free)]
           (if (= ok :ok)
             [ok res]
             (find-term t body (conj path 2) res free)))))

     (stx/app? u)
     (let [[u1 u2] u]
       (let [[ok res] (find-term t u1 (conj path 0) n-th free)]
         (if (= ok :ok)
           [ok res]
           (find-term t u2 (conj path 1) res free))))

     (stx/ref? u)
     (let [nbargs (dec (count u))]
       (loop [k 1, n-th n-th]
         (if (<= k nbargs)
           (let [[ok res] (find-term t (nth u k) (conj path k) n-th free)]
             (if (= ok :ok)
               [ok res]
               (recur (inc k) res)))
           [:ko n-th])))

     
     ;; all the other cases fail
     :else [:ko n-th])))

(declare body-build)

(defn build-subst-lambda 
  "Builds a lambda for substitutions of a subterm `$` within `u`
according to its `path`. The parameter `ty` is the type of the
substituted term."  
  [u ty path with-gensym]
  (let [$ (if with-gensym
            (gensym "$")
            '$)]
    (list 'λ [$ ty] (body-build $ path u)))) 
  
(defn body-build
  "This had to be a function with such a name"
  [tvar path u]
  (cond 
    ;; at the end of the path ...
    (= path []) tvar

    (stx/binder? u)
    (let [[b [x ty] body] u]
      (if (= (first path) 1)
        (list b [x (body-build tvar (rest path) ty)] body) 
        (list b [x ty] (body-build tvar (rest path) body))))

    (stx/app? u)
    (let [[u1 u2] u]
      (if (= (first path) 0)
        [(body-build tvar (rest path) u1) u2]
        [u1 (body-build tvar (rest path) u2)]))

    (stx/ref? u)
    (let [[dname & args] u
          vargs (vec args)
          before-args (subvec vargs 0 (dec (first path)))
          after-args (subvec vargs (first path))]
      (cons dname (concat before-args
                          (list (body-build tvar (rest path) (nth vargs (dec (first path)))))
                          after-args)))

    :else u))
    

       
