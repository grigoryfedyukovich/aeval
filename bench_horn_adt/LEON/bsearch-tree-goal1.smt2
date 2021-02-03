; (binary search) tree
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun tsize (Tree Int) Bool)
(assert (tsize leaf 0))
(assert (forall ((x Int) (r Tree) (l Tree) (m Tree) (sl Int) (sr Int))
	(=> (and (= m (node x l r)) (tsize l sl) (tsize r sr)) (tsize m (+ 1 (+ sl sr))))))

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
 
(assert (forall ((t Tree) (n Int) (r Tree) (ts Int) (rs Int))
	(=> (and (tinsert t n r) (tsize r rs) (tsize t ts) (not (= rs (+ 1 ts)))) false)))

(check-sat)
