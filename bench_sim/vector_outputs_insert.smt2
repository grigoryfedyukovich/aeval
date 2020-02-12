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

; lemma for len after insert
(assert (forall ((i Int) (y Elem) (xs Lst))
    (=> (<= i (len xs))
        (= (len (insert i y xs)) (+ (len xs) 1)))))

; lemma for get after insert
(assert (forall ((i Int) (j Int) (y Elem) (xs Lst))
    (=> (and (< i (len xs)) (< j (len xs)))
        (= (get i (insert j y xs))
           (ite (< i j) (get i xs)
           (ite (= i j) y
                        (get (- i 1) xs)))))))

(declare-fun i   () Int)
(declare-fun z   () Elem)

(declare-fun xs  () Lst)
(declare-fun n   () Int)
(declare-fun A   () (Array Int Elem))

(declare-fun xs1 () Lst)
(declare-fun n1  () Int)
(declare-fun A1  () (Array Int Elem))

; ; assumption R holds now
(assert (R xs n A))

; abstract precondition
(assert (<= i (len xs)))

; abstract transition
(assert (= xs1 (insert i z xs)))

; concrete transition
(assert (= n1 (+ n 1)))

; modified index
(assert (= (select A1 i) z))

; indices in prefix
(assert (forall ((k Int))
    (=> (< k i)
        (= (select A1 k) (select A k)))))

; indices in suffix
(assert (forall ((k Int))
    (=> (and (<= i k) (< k n))
        (= (select A1 (+ k 1)) (select A k)))))

(assert (not
    (= (<= i n) ; concrete precondition
       (R xs1 n1 A1))))

(check-sat)
