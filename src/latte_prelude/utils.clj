(ns latte-prelude.utils
  (:require [latte-kernel.syntax :as stx])
)

(defn find-term
  "Finds term `t` within term `u` recursively, constructing
  the `path` to the first occurrence. The lookup is simply wrt.
  structural equality."
  ([t u] (find-term t u []))

  ([t u path]
   (cond
     ;; found !
     (= t u) path

     (stx/binder? u)
     (let [[_ _ body] u]
       (find-term t body (conj path 2))) ;; element at index 2 in the term u

     (stx/app? u)
     (let [[u1 u2] u]
       (or (find-term t u1 (conj path 0))
           (find-term t u2 (conj path 1))))

     (stx/ref? u)
     (let [nbargs (dec (count u))]
       (loop [k 1]
         (if (<= k nbargs)
           (or (find-term t (nth u k) (conj path k))
               (recur (inc k)))
           false)))

     
     ;; all the other cases fail
     :else false)))



       
