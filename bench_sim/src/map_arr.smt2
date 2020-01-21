(declare-sort Key)
(declare-sort Value)

(declare-fun in () Key)
(declare-fun inv () Value)
(declare-fun out () Value)
(declare-fun s  () (Array Key Value))
(declare-fun s1 () (Array Key Value))

(declare-fun empty (Int) Value) ; Int - placeholder

; init

(assert
  (forall ((a Key)) (= (empty 0) (select s a))))

; get value

(assert
  (= out (select s in)))

; set value

(assert
  (= s1 (store s in inv)))

; remove

(assert
  (= s1 (store s in (empty 0))))
