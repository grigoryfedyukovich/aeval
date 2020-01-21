(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun allbutlast (Lst) Lst)
(assert (forall ((x Elem)) (= (allbutlast (cons x nil)) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (allbutlast (cons x (cons y xs))) (cons x (allbutlast (cons y xs))))))

(declare-fun last (Lst) Elem)
(assert (forall ((x Elem)) (= (last (cons x nil)) x)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (last (cons x (cons y xs))) (last (cons y xs)))))

; dequeue

(declare-fun xs () Lst)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun A () (Array Int Elem))

(declare-fun R (Lst Int Int (Array Int Elem)) Bool)

(assert (forall ((n Int) (m Int) (A (Array Int Elem)))
    (= (R nil m n A) (= m n))))

(assert (forall ((xs Lst) (h Elem) (m Int) (n Int) (A (Array Int Elem)))
    (= (R (cons h xs) m n A)
    (and (< m n)
         (= h (select A (- n 1)))
         (R xs m (- n 1) A)))))

; extra lemma
(assert (forall ((xs Lst) (m Int) (n Int) (A (Array Int Elem))) (=> (R xs m n A) (<= m n))))

; extra lemma:
(assert (forall ((m Int) (n Int) (n1 Int) (xs Lst) (h Elem) (A (Array Int Elem)))
  (=> (and (>= n1 n) (R xs m n A)) (R xs m n (store A n1 h)))))

(assert (and (R xs m n A) (distinct xs nil)))

(assert (not (R (allbutlast xs) (+ m 1) n A)))

(check-sat)
