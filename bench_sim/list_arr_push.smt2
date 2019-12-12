(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

; push

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun h () Elem)
(declare-fun n () Int)
(declare-fun n1 () Int)
(declare-fun A () (Array Int Elem))
(declare-fun A1 () (Array Int Elem))

(declare-fun R (Lst Int (Array Int Elem)) Bool)

(assert (forall ((n Int) (A (Array Int Elem))) (= (R nil n A) (= n 0))))

(assert (forall ((xs Lst) (h Elem) (n Int) (A (Array Int Elem)))
    (= (R (cons h xs) n A) (and (> n 0) (R xs (- n 1) A) (= h (select A (- n 1)))))))

;extra lemma:
(assert (forall ((n Int) (n1 Int) (xs Lst) (h Elem) (A (Array Int Elem)))
    (=> (and (>= n1 n) (R xs n A)) (R xs n (store A n1 h)))))

;extra lemma:
(assert (forall ((xs Lst) (n Int) (A (Array Int Elem)))
    (=> (R xs n A) (>= n 0))))

(assert (and (= xs1 (cons h xs)) (= A1 (store A n h)) (= n1 (+ n 1)) (R xs n A)))

(assert (not (R xs1 n1 A1)))
(check-sat)
