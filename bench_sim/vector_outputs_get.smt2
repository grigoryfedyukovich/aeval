(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun len (Lst) Int)
(declare-fun get (Int Lst) Elem)
(declare-fun remove (Int Lst) Lst)
(declare-fun insert (Int Elem Lst) Lst)

; definition of list length
(assert (forall ((xs Lst)) (= (len nil) 0))) ;  using forall just to parse
(assert (forall ((x Elem) (xs Lst)) (= (len (cons x xs)) (+ 1 (len xs)))))

; lemma: len is positive
(assert (forall ((xs Lst)) (>= (len xs) 0)))

; positional get
(assert (forall ((x Elem) (xs Lst))
        (= (get 0 (cons x xs)) x)))
(assert (forall ((i Int) (x Elem) (xs Lst))
    (=> (> i 0)
        (= (get i (cons x xs)) (get (- i 1) xs)))))

; positional remove
(assert (forall ((x Elem) (xs Lst))
        (= (remove 0 (cons x xs)) xs)))
(assert (forall ((i Int) (x Elem) (xs Lst))
    (=> (> i 0)
        (= (remove i (cons x xs)) (cons x (remove (- i 1) xs))))))

; positional insert
(assert (forall ((y Elem) (xs Lst))
        (= (insert 0 y xs) (cons y xs))))
(assert (forall ((i Int) (y Elem) (x Elem) (xs Lst))
    (=> (> i 0)
        (= (insert i y (cons x xs)) (cons x (insert (- i 1) y xs))))))

(declare-fun R (Lst Int (Array Int Elem)) Bool)

(assert (forall ((xs Lst) (n Int) (A (Array Int Elem)))
    (= (R xs n A)
       (and (= (len xs) n)
            (forall ((i Int))
                (=> (< i n) (= (select A i) (get i xs))))))))

(declare-fun xs () Lst)
(declare-fun i  () Int)
(declare-fun n  () Int)
(declare-fun A  () (Array Int Elem))

; assumption R holds now
(assert (R xs n A))

; expanded version works!
; (assert (= (len xs) n))
; (assert (forall ((i Int))
;                 (=> (< i n) (= (select A i) (get i xs)))))

; precondition of get
(assert (< i (len xs)))

(assert (not
    (= (get i xs)
       (select A i))))

(check-sat)
