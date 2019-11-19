(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun snoc (Lst Elem) Lst)
;(assert (forall ((x Elem)) (= (snoc nil x) (cons x nil))))
;(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (snoc (cons y xs) x) (cons y (snoc xs x)))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)
(declare-fun out () Elem)

; isempty

(assert (= xs nil))

; enqueue

(assert (= xs1 (snoc xs in)))

; dequeue

(assert (= xs (cons out xs1)))

