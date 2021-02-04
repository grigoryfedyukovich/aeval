(set-logic HORN)

; (binary search) tree
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun tinsert (Tree Int Tree) Bool)
(assert (forall ((i Int)) (tinsert leaf i (node i leaf leaf))))
(assert (forall ((r Tree) (l Tree) (d Int) (i Int) (x Tree) (m Tree)) 
	(=> (and (tinsert r i x) (< d i) (= m (node d l x))) (tinsert (node d l r) i m))))
(assert (forall ((r Tree) (l Tree) (d Int) (i Int) (y Tree) (m Tree)) 
	(=> (and (tinsert l i y) (>= d i) (= m (node d y r))) (tinsert (node d l r) i m))))

(declare-fun tcontains (Tree Int Bool) Bool)
(assert (forall ((i Int)) (tcontains leaf i false)))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int))
	(=> (= d i) (tcontains (node d l r) i true))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int))
	(=> (tcontains l i true) (tcontains (node d l r) i true))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int))
	(=> (tcontains r i true) (tcontains (node d l r) i true))))

; conjecture
(assert (forall ((x Tree) (i Int) (y Tree) (r Bool))
	(=> (and (tinsert x i y) (tcontains y i r) (not r)) false))); G-bsearch-tree-6 

(check-sat)
