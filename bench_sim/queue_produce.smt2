(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

; enqueue

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun h () Elem)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun A () (Array Int Elem))
(declare-fun A1 () (Array Int Elem))

(declare-fun R (Lst Int Int (Array Int Elem)) Bool)

(assert (forall ((n Int) (m Int) (A (Array Int Elem)))
    (= (R nil m n A) (= m n))))

(assert (forall ((xs Lst) (h Elem) (m Int) (n Int) (A (Array Int Elem)))
    (= (R (cons h xs) m n A)
      (and (< m n)
         (= h (select A (- n 1)))
         (R xs m (- n 1) A)))))

; extra lemma:
(assert (forall ((m Int) (n Int) (n1 Int) (xs Lst) (h Elem) (A (Array Int Elem)))
    (=> (and (>= n1 n) (R xs m n A)) (R xs m n (store A n1 h)))))

; extra lemma
(assert (forall ((xs Lst) (m Int) (n Int) (A (Array Int Elem)))
    (=> (R xs m n A) (<= m n))))

(assert (and (R xs m n A)
             (= xs1 (cons h xs))
             (= A1 (store A n h))))

(assert (not (R xs1 m (+ n 1) A1)))

(check-sat)
