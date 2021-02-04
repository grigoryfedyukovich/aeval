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

(declare-fun tsorted (Tree) Bool)
(assert (tsorted leaf))
(assert (forall ((d Int) (l Tree) (r Tree)) (= (tsorted (node d l r)) (and (tsorted l) (tsorted r)
                                                                           (forall ((x Int)) (=> (tcontains l x true) (<= x d)))
                                                                           (forall ((x Int)) (=> (tcontains r x true) (< d x)))))))
                                                                           
(declare-fun tmember (Tree Int Bool) Bool)
(assert (forall ((x Int)) (tmember leaf x false)))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int)) 
	(=> (= i d) (tmember (node d l r) i true))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int)) 
	(=> (and (< d i) (tmember r i true)) (tmember (node d l r) i true))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int)) 
	(=> (and (< i d) (tmember l i true)) (tmember (node d l r) i true))))
                              
; conjecture
(assert (forall ((i Int) (x Tree) (r Bool) (s Bool))
	(=> (and (tsorted x) (tcontains x i r) (tmember x i s) (not (= r s))) false))) ; G-bsearch-tree-11 

(check-sat)