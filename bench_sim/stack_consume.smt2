(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

; pop

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun h () Elem)
(declare-fun n () Int)
(declare-fun A () (Array Int Elem))

(declare-fun R (Lst Int (Array Int Elem)) Bool)

(assert (forall ((n Int) (A (Array Int Elem))) (= (R nil n A) (= n 0))))

(assert (forall ((xs Lst) (h Elem) (n Int) (A (Array Int Elem)))
    (= (R (cons h xs) n A) (and (> n 0) (R xs (- n 1) A) (= h (select A (- n 1)))))))

(assert (and (= xs1 (cons h xs)) (R xs1 n A)))

(assert (not (R xs (- n 1) A)))
(check-sat)
