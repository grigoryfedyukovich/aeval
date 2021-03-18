(set-logic HORN)

; lists      
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst Lst) Bool)
(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst))
    (=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))

(declare-fun len (Lst Int) Bool)
(assert (len nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int))
           (=> (and (= xs (cons x ys)) (len ys l)) (len xs (+ l 1)))))

; (binary search) tree
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

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

(declare-fun tcontains (Tree Int Bool) Bool)
(assert (forall ((i Int)) (tcontains leaf i false)))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int))
	(=> (= d i) (tcontains (node d l r) i true))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int))
	(=> (tcontains l i true) (tcontains (node d l r) i true))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int))
	(=> (tcontains r i true) (tcontains (node d l r) i true))))

(declare-fun tsorted (Tree Bool) Bool)
(assert (tsorted leaf true))
(assert (forall ((d Int) (l Tree) (r Tree) (x Int) (y Int))
	(=> (and (tsorted l true) (tsorted r true) (tcontains l x true) (tcontains r x true)
		(<= x d) (< d x)) (tsorted (node d l r) true))))
                                                                           
; conjecture
(assert (forall ((x Lst) (y Tree))
	(=> (and (tinsert-all leaf x y) (not (tsorted y true))) false))) ; G-bsearch-tree-14 

(check-sat)
