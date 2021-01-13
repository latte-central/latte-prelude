(ns latte-prelude.utils
  (:require [latte-kernel.syntax :as stx])
)

(defn find-term
  "Finds term `t` within term `u` recursively, constructing
  the `path` to the first occurrence. The lookup is simply wrt.
  structural equality."
  ([t u] (find-term t u [] #{}))

  ([t u path bound]
   (cond
     ;; first, we try with structural equality
     (and (not (bound t))
          (= t u)) 
     path

     ;; let's try with alpha-norm
     (and (not (bound t))
          (stx/alpha-eq? t u))
     path

     (stx/binder? u)
     (let [[_ [x ty] body] u]
       (or (find-term t ty (conj path 1) bound)
           (find-term t body (conj path 2) (conj bound x))))

     (stx/app? u)
     (let [[u1 u2] u]
       (or (find-term t u1 (conj path 0) bound)
           (find-term t u2 (conj path 1) bound)))

     (stx/ref? u)
     (let [nbargs (dec (count u))]
       (loop [k 1]
         (if (<= k nbargs)
           (or (find-term t (nth u k) (conj path k) bound)
               (recur (inc k)))
           false)))

     
     ;; all the other cases fail
     :else false)))

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
                          (list (body-build tvar (rest path) (nth vargs (first path))))
                          after-args)))

    :else u))
    

       
