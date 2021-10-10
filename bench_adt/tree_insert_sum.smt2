(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun tinsert (Tree Int) Tree)
(assert (forall ((i Int)) (= (tinsert leaf i) (node i leaf leaf))))
(assert (forall ((r Tree) (l Tree) (d Int) (i Int)) (= (tinsert (node d l r) i) (ite (< d i) (node d l (tinsert r i)) (node d (tinsert l i) r)))))

(declare-fun tsum (Tree) Int)
(assert (= (tsum leaf) 0))
(assert (forall ((x Int) (l Tree) (r Tree)) (= (tsum (node x l r)) (+ x (+ (tsum l) (tsum r))))))

(assert (not (forall ((t Tree) (n Int)) (= (tsum (tinsert t n)) (+ n (tsum t))))))
(check-sat)
