(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-fun interleave (list list) list)
(declare-fun evens (list) list)
(declare-fun odds (list) list)
(assert
  (not
    (forall ((xs list)) (= (interleave (evens xs) (odds xs)) xs))))
(assert
  (forall ((x list) (y list))
    (= (interleave x y)
      (ite (is-cons x) (cons (head x) (interleave y (tail x))) y))))
(assert
  (forall ((x list))
    (= (evens x)
      (ite (is-cons x) (cons (head x) (odds (tail x))) nil))))
(assert
  (forall ((x list))
    (= (odds x) (ite (is-cons x) (evens (tail x)) nil))))
(check-sat)
