(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun reverse (Lst) Lst)

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

; dequeue (non-reverse case)

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
      (= xs  (cons out (reverse ys1))))))
