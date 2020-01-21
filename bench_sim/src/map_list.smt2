(declare-sort Key)
(declare-sort Value)
(declare-datatypes () ((Pair (pair (key Key) (value Value)))))
(declare-datatypes () ((Lst (cons (head Pair) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Key)
(declare-fun inv () Value)
(declare-fun out () Value)

(declare-fun empty (Int) Value) ; Int - placeholder

(declare-fun get (Key Lst) Value)
(assert (forall ((x Key)) (= (get x nil) (empty 0))))
(assert (forall ((x Key) (y Key) (z Value) (xs Lst))
  (= (get x (cons (pair y z) xs)) (ite (= x y) z (get x xs)))))

(declare-fun set (Key Value Lst) Lst)
(assert (forall ((x Key) (v Value)) (= (set x v nil) (cons (pair x v) nil))))
(assert (forall ((x Key) (v Value) (y Key) (z Value) (xs Lst))
  (= (set x v (cons (pair y z) xs))
     (ite (= x y) (cons (pair x v) xs) (cons (pair y z) (set x v xs))))))

(declare-fun remove (Key Lst) Lst)
(assert (forall ((x Key)) (= (remove x nil) nil)))
(assert (forall ((x Key) (y Key) (v Value) (xs Lst))
  (= (remove x (cons (pair y v) xs)) (ite (= x y) xs (cons (pair y v) (remove x xs))))))

; init

(assert
  (= xs nil))

; get value

(assert
  (= out (get in xs)))

; set value

(assert
  (= xs1 (set in inv xs)))

; remove

(assert
  (= xs1 (remove in xs)))
