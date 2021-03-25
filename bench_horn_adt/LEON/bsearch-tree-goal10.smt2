(set-logic HORN)

; (binary search) tree
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun tinsert (Tree Int Tree) Bool)
(assert (forall ((i Int)) (tinsert leaf i (node i leaf leaf))))
(assert (forall ((r Tree) (l Tree) (d Int) (i Int) (x Tree) (m Tree)) 
	(=> (and (tinsert r i x) (< d i) (= m (node d l x))) (tinsert (node d l r) i m))))
(assert (forall ((r Tree) (l Tree) (d Int) (i Int) (y Tree) (m Tree)) 
	(=> (and (tinsert l i y) (>= d i) (= m (node d y r))) (tinsert (node d l r) i m))))

(declare-fun tmember (Tree Int Bool) Bool)
(assert (forall ((x Int)) (tmember leaf x false)))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int)) 
	(=> (= i d) (tmember (node d l r) i true))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int)) 
	(=> (and (< d i) (tmember r i true)) (tmember (node d l r) i true))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int)) 
	(=> (and (< i d) (tmember l i true)) (tmember (node d l r) i true))))

(assert (forall ((i Int) (x Tree) (j Int) (r Bool) (s Bool) (t Bool) (y Tree) (a Bool) (b Bool))
	(=> (and (tmember x j b) (tinsert x i y) (tmember y j true) (>= (- i j) 1) (not (= b true))) false)))

(assert (forall ((i Int) (x Tree) (j Int) (r Bool) (s Bool) (t Bool) (y Tree) (a Bool) (b Bool))
	(=> (and (tmember x j b) (tinsert x i y) (tmember y j true) (>= (- j i) 1) (not (= b true))) false)))

(assert (forall ((i Int) (x Tree) (j Int) (r Bool) (s Bool) (t Bool) (y Tree) (a Bool) (b Bool))
	(=> (and (tmember x j true) (tinsert x i y) (tmember y j a) (not (= a true))) false)))

(assert (forall ((i Int) (x Tree) (j Int) (r Bool) (s Bool) (t Bool) (y Tree) (a Bool) (b Bool))
	(=> (and (tmember x i b) (tinsert x i y) (tmember y i a) (not (= a true))) false)))

(check-sat)