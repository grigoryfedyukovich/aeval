(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun R (Lst Int (Array Int Elem)) Bool)

(assert (forall ((n Int) (A (Array Int Elem))) (= (R nil n A) (= n 0))))

(assert (forall ((xs Lst) (h Elem) (n Int) (A (Array Int Elem)))
    (= (R (cons h xs) n A) (and (> n 0) (R xs (- n 1) A) (= h (select A (- n 1)))))))

(assert (not (forall ((xs Lst) (n Int) (A (Array Int Elem)))
  (=> (R xs n A) (>= n 0)))))

(check-sat)
