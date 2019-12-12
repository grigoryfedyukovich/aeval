(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun num (Elem Lst) Int)
(assert (forall ((x Elem)) (= (num x nil) 0)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (num x (cons y xs)) (ite (= x y) (+ 1 (num x xs)) (num x xs)))))

(declare-fun R (Lst (Array Elem Int)) Bool)
(assert (forall ((s (Array Elem Int)) (a Elem)) (= (R nil s) (forall ((a Elem)) (= (select s a) 0)))))
(assert (forall ((xs Lst) (in Elem) (s (Array Elem Int)))
  (= (R (cons in xs) s)
    (and (= (select s in) (+ 1 (num in xs))) (R xs (store s in (+ (- 1) (select s in))))))))

; extra

(assert (forall ((xs Lst) (in Elem) (s (Array Elem Int)))
  (=> (R xs s) (= (select s in) (num in xs)))))

(declare-fun xs () Lst)
(declare-fun in () Elem)
(declare-fun s () (Array Elem Int))

(assert (R xs s))
(assert (not (R (cons in xs) (store s in (+ 1 (select s in))))))
