(set-logic HORN)
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (nil))))
(declare-fun size (Tree Int) Bool)

(assert (size nil 0))
(assert (forall ((x Int) (r Tree) (l Tree) (m Tree) (sl Int) (sr Int))
           (=> (and (= m (node x l r)) (size l sl) (size r sr)) (size m (+ sl sr)))))

(assert (forall ((s Int) (m Tree))
       (=> (and (size m s) (not (>= s 0))) false)))
(check-sat)
