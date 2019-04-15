(declare-sort sk_a 0)
(declare-sort sk_b 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk_b) (tail2 list2)))))
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-fun apply1 (fun1 sk_a) list2)
(declare-fun return (sk_a) list)
(declare-fun append (list2 list2) list2)
(declare-fun bind (list fun1) list2)
(assert
  (not
    (forall ((x sk_a) (f fun1)) (= (bind (return x) f) (apply1 f x)))))
(assert (forall ((x sk_a)) (= (return x) (cons x nil))))
(assert
  (forall ((x list2) (y list2))
    (= (append x y)
      (ite (is-cons2 x) (cons2 (head2 x) (append (tail2 x) y)) y))))
(assert
  (forall ((x list) (y fun1))
    (= (bind x y)
      (ite
        (is-cons x) (append (apply1 y (head x)) (bind (tail x) y)) nil2))))
(check-sat)
