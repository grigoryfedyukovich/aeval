(declare-sort Elem)

(declare-fun in () Elem)
(declare-fun out () Elem)
(declare-fun s  () (Array Elem Bool))
(declare-fun s1 () (Array Elem Bool))

(declare-fun empty () (Array Elem Bool))
; (assert (forall ((a Elem)) (not (select empty a))))

; init

(assert
  (= s empty)

; contains

(assert
  (and
    (= out (select s in))
    (= s1  s)))

; insert

(assert
  (= s1 (store s in true)))

; remove

(assert
  (= s1 (store s in false)))
