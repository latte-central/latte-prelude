(ns latte-prelude.fun
  "A **function** with domain `T` and codomain `U` 
  has type `(==> T U)`.

   This namespace provides some important properties about such
  functions."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [definition defaxiom defthm defimplicit
                                          proof assume have pose qed]]
            [latte-prelude.prop :as p :refer [and or not]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]))

(definition injective
  "An injective function."
  [[?T :type] [?U :type] [f (==> T U)]]
  (forall [x y T]
    (==> (equal (f x) (f y))
         (equal x y))))

(definition surjective
  "A surjective function."
  [[?T :type] [?U :type] [f (==> T U)]]
  (forall [y U] (exists [x T] (equal (f x) y))))

(definition bijective
  "A bijective function."
  [[?T :type] [?U :type] [f (==> T U)]]
  (and (injective f)
       (surjective f)))

(defthm bijective-is-surjective
  "A bijection is a surjection."
  [[?T :type] [?U :type] [f (==> T U)]]
  (==> (bijective f)
       (surjective f)))

(proof 'bijective-is-surjective-thm
  (assume [H (bijective f)]
    (have <a> (surjective f) :by (p/and-elim-right H)))
  (qed <a>))

(defthm bijective-is-injective
  "A bijection is an injection."
  [[?T :type] [?U :type] [f (==> T U)]]
  (==> (bijective f)
       (injective f)))

(proof 'bijective-is-injective-thm
  (assume [H (bijective f)]
    (have <a> (injective f) :by (p/and-elim-left H)))
  (qed <a>))

(definition compose
  "The composition of two functions."
  [[?T :type] [?U :type] [?V :type] [f (==> U V)] [g [==> T U]]]
  (lambda [x T] (f (g x))))

(defthm compose-injective
  "The composition of two injective functions is injective."
  [[?T :type] [?U :type] [?V :type] [f (==> U V)] [g [==> T U]]]
  (==> (injective f)
       (injective g)
       (injective (compose f g))))

(proof 'compose-injective-thm  
  (assume [Hf (injective f)
           Hg (injective g)]
    (assume [x T
             y T
             Hinj (equal ((compose f g) x)
                         ((compose f g) y))]
      (have <a> (equal (f (g x)) (f (g y))) :by Hinj)
      (have <b> (equal (g x) (g y))
            :by (Hf (g x) (g y) <a>))
      (have <c> (equal x y)
            :by (Hg x y <b>))))
  (qed <c>))

(defthm injective-single
  "An injective function has at most one antecedent for each image."
  [[?T :type] [?U :type] [f (==> T U)]]
  (==> (injective f)
       (forall [y U] (q/single (lambda [x T] (equal (f x) y))))))

(proof 'injective-single-thm   
  (assume [Hf (injective f)]
    (assume [y U]
      (assume [x1 T
               x2 T
               Hx1 (equal (f x1) y)
               Hx2 (equal (f x2) y)]
        (have <a1> (equal y (f x2)) :by (eq/eq-sym Hx2))
        (have  <a> (equal (f x1) (f x2))
               :by (eq/eq-trans Hx1 <a1>))
        (have <b> (equal x1 x2) :by (Hf x1 x2 <a>)))))
  (qed <b>))

(defthm bijective-unique
  "A bijective function has exactly one antecedent for each image."
  [[?T :type] [?U :type] [f (==> T U)]]
  (==> (bijective f)
       (forall [y U] (q/unique (lambda [x T] (equal (f x) y))))))

(proof 'bijective-unique-thm  
  (assume [Hf (bijective f)]
    (have <a> (injective f)
          :by ((bijective-is-injective f) Hf))
    (have <b> (surjective f)
          :by ((bijective-is-surjective f) Hf))
    (assume [y U]
      (have <c> (q/ex (lambda [x T] (equal (f x) y)))
            :by (<b> y))
      (have <d> (q/single (lambda [x T] (equal (f x) y)))
            :by ((injective-single f) <a> y))
      (have <e> (q/unique (lambda [x T] (equal (f x) y)))
            :by (p/and-intro <c> <d>))))
  (qed <e>))

(definition inverse
  "The inverse of bijective function `f`."
  [[?T :type] [?U :type] [f (==> T U)] [b (bijective f)]]
  (lambda [y U]
    (q/the (lambda [x T] (equal (f x) y))
           ((bijective-unique f) b y))))

(defthm inverse-prop
  "The basic property of the inverse of a bijective function `f`."
  [[?T :type] [?U :type] [f (==> T U)] [b (bijective f)]]
  (forall [y U] (equal (f ((inverse f b) y)) y)))

(proof 'inverse-prop-thm  
  (assume [y U]
    (have <a> (equal (f ((inverse f b) y)) y)
          :by (q/the-prop (lambda [z T] (equal (f z) y))
                          (((bijective-unique f) b) y))))
  (qed <a>))

(defthm inverse-prop-conv
  "The basic property of the inverse function,
 the converse of [[inverse-prop]]."
  [[?T :type] [?U :type] [f (==> T U)] [b (bijective f)]]
  (forall [x T] (equal ((inverse f b) (f x)) x)))

(proof 'inverse-prop-conv-thm  
  (assume [x T]
    (have <a> (equal (f ((inverse f b) (f x))) (f x))
          :by ((inverse-prop f b) (f x)))
    (have <b> (equal ((inverse f b) (f x)) x)
          :by (((bijective-is-injective f) b)
               ((inverse f b) (f x)) x
               <a>)))
  (qed <b>))

(defthm inverse-surjective
  "The inverse function of a bijection, is surjective."
  [[?T :type] [?U :type] [f (==> T U)] [b (bijective f)]]
  (surjective (inverse f b)))

(proof 'inverse-surjective-thm 
  (have <a> (injective f) :by ((bijective-is-injective f) b))
  (pose inv-f := (inverse f b))
  (assume [x T]
    (pose y := (f x))
    (have <b> (equal (f (inv-f y)) (f x))
          :by ((inverse-prop f b) (f x)))
    (have <c> (equal (inv-f y) x) :by (<a> (inv-f y) x <b>))
    (have <d> (exists [y U] (equal (inv-f y) x))
          :by ((q/ex-intro (lambda [z U] (equal (inv-f z) x)) y)
               <c>)))
  (qed <d>))

(defthm inverse-injective
  "The inverse function of a bijection, is injective."
  [[?T :type] [?U :type] [f (==> T U)] [b (bijective f)]]
  (injective (inverse f b)))

(proof 'inverse-injective-thm 
  (pose inv-f := (inverse f b))
  (assume [x U
           y U
           Hxy (equal (inv-f x) (inv-f y))]
    (have <a> (equal (f (inv-f x)) (f (inv-f y)))
          :by (eq/eq-cong f Hxy))
    (have <b> (equal (f (inv-f x)) x)
          :by ((inverse-prop f b) x))
    (have <c> (equal x (f (inv-f x)))
          :by (eq/eq-sym <b>))
    (have <d> (equal (f (inv-f y)) y)
          :by ((inverse-prop f b) y))
    (have <e> (equal x (f (inv-f y)))
          :by (eq/eq-trans <c> <a>))
    (have <f> (equal x y)
          :by (eq/eq-trans <e> <d>)))
  (qed <f>))

(defthm inverse-bijective
  "The inverse of a bijection is a bijection."
  [[?T :type] [?U :type] [f (==> T U)] [b (bijective f)]]
  (bijective (inverse f b)))

(proof 'inverse-bijective-thm
  (have <a> _ :by (p/and-intro (inverse-injective f b)
                               (inverse-surjective f b)))
  (qed <a>))




