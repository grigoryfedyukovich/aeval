(set-logic HORN)

; lists      
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun len (Lst Int) Bool)
(assert (len nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int))
           (=> (and (= xs (cons x ys)) (len ys l)) (len xs (+ l 1)))))

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

(declare-fun tremove (Tree Int Tree) Bool)
(assert (forall ((i Int)) (tremove leaf i leaf)))
(assert (forall ((i Int) (d Int) (l Tree) (r Tree) (m Tree)) 
	(=> (and (< i d) (tremove l i m)) (tremove (node d l r) i (node d m r)))))
(assert (forall ((i Int) (d Int) (l Tree) (r Tree) (m Tree)) 
	(=> (and (< d i) (tremove r i m)) (tremove (node d l r) i (node d l m)))))
(assert (forall ((d Int) (r Tree)) (tremove (node d leaf r) d r)))
(assert (forall ((d Int) (ld Int) (ll Tree) (lr Tree) (r Tree) (m Tree))
	(=> (tremove (node ld ll lr) ld m) (tremove (node d (node ld ll lr) r) d (node ld m r)))))

; conjecture
(assert (forall ((t Tree) (n Int) (r Tree) (rs Int) (ts Int))
	(=> (and (tremove t n r) (tsize t ts) (tsize r rs) (not (<= rs ts))) false))) ; G-bsearch-tree-4 

(check-sat)
