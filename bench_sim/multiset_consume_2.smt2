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

(declare-fun remove (Elem Lst) Lst)
(assert (forall ((x Elem)) (= (remove x nil) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (remove x (cons y xs)) (ite (= x y) xs (cons y (remove x xs))))))

; extras

(assert (forall ((xs Lst) (in Elem) (s (Array Elem Int)))
  (=> (R xs s) (= (select s in) (num in xs)))))

(assert (forall ((xs Lst) (in Elem)) (>= (num in xs) 0)))

(assert (forall ((xs Lst) (a (Elem)) (b (Elem)))
  (=> (distinct a b) (= (num b (remove a xs)) (num b xs)))))

(assert (forall ((xs Lst) (a (Elem)) (b (Elem)))
  (=> (distinct a b) (= (num b (cons a xs)) (num b xs)))))

(declare-fun xs () Lst)
(declare-fun in () Elem)
(declare-fun s () (Array Elem Int))

(assert (R xs s))
(assert (not (R (remove in xs) (ite (> (select s in) 0) (store s in (+ -1 (select s in))) s))))
