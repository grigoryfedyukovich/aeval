(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun allbutlast (Lst) Lst)
(assert (forall ((x Elem)) (= (allbutlast (cons x nil)) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (allbutlast (cons x (cons y xs))) (cons x (allbutlast (cons y xs))))))

(declare-fun last (Lst) Elem)
(assert (forall ((x Elem)) (= (last (cons x nil)) x)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (last (cons x (cons y xs))) (last (cons y xs)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Elem) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

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
(assert (forall ((xs Lst)) (=> (not (= xs nil)) (= xs (append (allbutlast xs) (cons (last xs) nil))))))

; not used
(assert (not (forall ((xs Lst) (m Int) (n Int) (A (Array Int Elem))) (=> (and (distinct xs nil) (R xs m n A)) (R (allbutlast xs) (+ m 1) n A)))))

(check-sat)
