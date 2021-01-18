(set-logic HORN)
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun size (Tree Int) Bool)
(declare-fun insert (Tree Int Tree) Bool)

(assert (size leaf 0))
(assert (forall ((x Int) (r Tree) (l Tree) (m Tree) (sl Int) (sr Int))
	(=> (and (= m (node x l r)) (size l sl) (size r sr)) (size m (+ 1 (+ sl sr))))))

(assert (forall ((i Int)) (insert leaf i (node i leaf leaf))))
(assert (forall ((r Tree) (l Tree) (d Int) (i Int) (x Tree) (m Tree)) 
	(=> (and (insert r i x) (< d i) (= m (node d l x))) (insert (node d l r) i m))))

(assert (forall ((r Tree) (l Tree) (d Int) (i Int) (y Tree) (m Tree)) 
	(=> (and (insert l i y) (>= d i) (= m (node d y r))) (insert (node d l r) i m))))

(assert (forall ((t Tree) (n Int) (ts Int) (rs Int) (r Tree)) 
	(=> (and (size t ts) (insert t n r) (size r rs) (not (= rs (+ 1 ts)))) false)))

(check-sat)
