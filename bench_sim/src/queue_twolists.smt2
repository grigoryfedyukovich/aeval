(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun snoc (Lst Elem) Lst)
;(assert (forall ((x Elem)) (= (snoc nil x) (cons x nil))))
;(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (snoc (cons y xs) x) (cons y (snoc xs x)))))

(declare-fun reverse (Lst) Lst)
;(assert (= (reverse nil) nil))
;(assert (forall ((x Elem) Elem) (xs Lst)) (= (reverse (cons x xs)) (snoc (reverse xs) x)))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun ys () Lst)
(declare-fun ys1 () Lst)
(declare-fun in () Elem)
(declare-fun out () Elem)

; isempty

(assert
  (and
    (= xs nil)
    (= ys nil)))

; enqueue

(assert
  (and
    (= xs1 (cons in xs))
    (= ys1 ys)))

; dequeue

(assert
  (or
    (and
      (distinct ys nil)
      (= xs1 xs)
      (= ys  (cons out ys1)))
    (and
      (= ys nil)
      (distinct xs nil)
      (= xs1 nil)
      (= xs  (reverse (cons out ys1))))))
