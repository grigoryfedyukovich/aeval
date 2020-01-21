(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)
(declare-fun out () Elem)
(declare-fun outb () Int)

(declare-fun num (Elem Lst) Int)
(assert (forall ((x Elem)) (= (num x nil) 0)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (num x (cons y xs)) (ite (= x y) (+ 1 (num x xs)) (num x xs)))))

(declare-fun remove (Elem Lst) Lst)
(assert (forall ((x Elem)) (= (remove x nil) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (remove x (cons y xs)) (ite (= x y) xs (cons y (remove x xs))))))

; extras

(assert (forall ((xs Lst) (in Elem)) (>= (num in xs) 0)))

(assert (forall ((xs Lst) (a (Elem)) (b (Elem)))
  (=> (distinct a b) (= (num b (remove a xs)) (num b xs)))))

(assert (forall ((xs Lst) (a (Elem)) (b (Elem)))
  (=> (distinct a b) (= (num b (cons a xs)) (num b xs)))))

; init

(assert
  (= xs nil))

; num of elements

(assert
  (= outb (num in xs)))

; insert

(assert
  (= xs1 (cons in xs)))

; remove

(assert
  (= xs1 (remove in xs)))
