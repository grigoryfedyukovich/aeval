(declare-sort Elem)

(declare-fun in () Elem)
(declare-fun out () Elem)
(declare-fun outb () Bool)
(declare-fun s  () (Array Elem Bool))
(declare-fun s1 () (Array Elem Bool))

; init

(assert
  (forall ((a Elem)) (not (select s a))))

; contains

(assert
  (= outb (select s in)))

; insert

(assert
  (= s1 (store s in true)))

; remove

(assert
  (= s1 (store s in false)))
