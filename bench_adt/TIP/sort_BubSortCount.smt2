(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first Bool) (second list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun count (Int list) Nat)
(declare-fun bubble (list) Pair)
(declare-fun bubsort (list) list)
(assert
  (not
    (forall ((x Int) (y list)) (= (count x (bubsort y)) (count x y)))))
(assert
  (forall ((x Int) (y list))
    (= (count x y)
      (ite
        (is-cons y)
        (ite (= x (head y)) (S (count x (tail y))) (count x (tail y)))
        Z))))
(assert
  (forall ((x list))
    (= (bubble x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (ite
            (<= (head x) (head (tail x)))
            (let ((y (bubble (cons (head (tail x)) (tail (tail x))))))
              (Pair2 (first y) (cons (head x) (second y))))
            (Pair2 true
              (cons (head (tail x))
                (second (bubble (cons (head x) (tail (tail x))))))))
          (Pair2 false (cons (head x) nil)))
        (Pair2 false nil)))))
(assert
  (forall ((x list))
    (= (bubsort x)
      (let ((y (bubble x))) (ite (first y) (bubsort (second y)) x)))))
(check-sat)
