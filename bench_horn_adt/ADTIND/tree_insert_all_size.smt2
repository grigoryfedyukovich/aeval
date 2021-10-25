(set-logic HORN)
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun size (Tree Int) Bool)
(declare-fun insert (Tree Int Tree) Bool)
(declare-fun insert-all (Tree Lst Tree) Bool)

(assert (size leaf 0))
(assert (forall ((x Int) (r Tree) (l Tree) (m Tree) (sl Int) (sr Int))
	(=> (and (= m (node x l r)) (size l sl) (size r sr)) (size m (+ 1 (+ sl sr))))))

(assert (forall ((i Int)) (insert leaf i (node i leaf leaf))))

(assert (forall ((r Tree) (l Tree) (d Int) (i Int) (x Tree) (y Tree) (m Tree)) 
	(=> (and (insert r i x) (insert l i y) 
		(= m (ite (< d i) (node d l x) (node d y r)))) (insert (node d l r) i m))))

(assert (forall ((x Tree)) (insert-all x nil x)))
(assert (forall ((x Tree) (n Int) (ls Lst) (xs Lst) (z Tree) (y Tree)) 
	(=> (and (insert-all x ls y) (= xs (cons n ls)) (insert y n z)) (insert-all x xs z))))

;extra lemmas
(assert (forall ((t Tree) (n Int) (st Int) (x Tree) (sx Int)) 
	(=> (and (size t st) (insert t n x) (size x sx) (not (= sx (+ 1 st)))) false)))

(assert (forall ((l Lst) (t Tree) (i Int) (x Tree) (m Int) (n Int))
	(=> (and (size t n) (insert t i x) (size x m) (not (= m (+ 1 n)))) false)))

(check-sat)
