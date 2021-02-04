(set-logic HORN)

; lists      
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))


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


(declare-fun tinsert-all (Tree Lst Tree) Bool)
(assert (forall ((x Tree)) (tinsert-all x nil x)))
(assert (forall ((x Tree) (n Int) (ls Lst) (xs Lst) (z Tree) (y Tree)) 
	(=> (and (tinsert-all x ls y) (= xs (cons n ls)) (tinsert y n z)) (tinsert-all x xs z))))

; conjecture
(assert (forall ((l Lst) (t Tree) (ts Int) (r Tree) (rs Int)) 
	(=> (and (tsize t ts) (tinsert-all t l r) (tsize r rs) (not (<= ts rs))) false))) ; G-bsearch-tree-2 

(check-sat)
