(declare-sort Elem)

(declare-fun in () Elem)
(declare-fun in2 () Elem)
(declare-fun out () Elem)
(declare-fun out2 () Elem)
(declare-fun out3 () Elem)
(declare-fun n () Int)
(declare-fun n1 () Int)
(declare-fun A () (Array Int Elem))
(declare-fun A1 () (Array Int Elem))

; isempty

(assert (= n 0))

; push

(assert
  (and
  (= A1 (store (store A n in2) (+ n 1) in))
  (= n1 (+ n 2))))

; pop

(assert
  (and
    (> n 2)
    (= n1 (- n 3))
    (= A1 A)
    (= out (select A (- n 1)))
    (= out2 (select A (- n 2)))
    (= out3 (select A (- n 3)))))
