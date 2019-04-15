(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes ()
  ((Tree (TNode (TNode_0 Tree) (TNode_1 Int) (TNode_2 Tree))
     (TNil))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun flatten (Tree list) list)
(declare-fun count (Int list) Nat)
(declare-fun add (Int Tree) Tree)
(declare-fun toTree (list) Tree)
(declare-fun tsort (list) list)
(assert
  (not
    (forall ((x Int) (y list)) (= (count x (tsort y)) (count x y)))))
(assert
  (forall ((x Tree) (y list))
    (= (flatten x y)
      (ite
        (is-TNil x) y
        (flatten (TNode_0 x)
          (cons (TNode_1 x) (flatten (TNode_2 x) y)))))))
(assert
  (forall ((x Int) (y list))
    (= (count x y)
      (ite
        (is-cons y)
        (ite (= x (head y)) (S (count x (tail y))) (count x (tail y)))
        Z))))
(assert
  (forall ((x Int) (y Tree))
    (= (add x y)
      (ite
        (is-TNil y) (TNode TNil x TNil)
        (ite
          (<= x (TNode_1 y))
          (TNode (add x (TNode_0 y)) (TNode_1 y) (TNode_2 y))
          (TNode (TNode_0 y) (TNode_1 y) (add x (TNode_2 y))))))))
(assert
  (forall ((x list))
    (= (toTree x)
      (ite (is-cons x) (add (head x) (toTree (tail x))) TNil))))
(assert (forall ((x list)) (= (tsort x) (flatten (toTree x) nil))))
(check-sat)
