(set-logic HORN)
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun sum (Tree Int) Bool)
(declare-fun insert (Tree Int Tree) Bool)

(assert (sum leaf 0))
(assert (forall ((x Int) (r Tree) (l Tree) (m Tree) (sl Int) (sr Int))
	(=> (and (= m (node x l r)) (sum l sl) (sum r sr)) (sum m (+ x (+ sl sr))))))

(assert (forall ((i Int)) (insert leaf i (node i leaf leaf))))
(assert (forall ((r Tree) (l Tree) (d Int) (i Int) (x Tree) (y Tree) (m Tree)) 
	(=> (and (insert r i x) (insert l i y) 
		(= m (ite (< d i) (node d l x) (node d y r)))) (insert (node d l r) i m))))

(assert (forall ((t Tree) (n Int) (ts Int) (rs Int) (r Tree)) 
	(=> (and (sum t ts) (insert t n r) (sum r rs) (not (= rs (+ n ts)))) false)))

(check-sat)