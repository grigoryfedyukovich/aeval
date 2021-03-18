(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-fun length (Lst Int) Bool)

(assert (length nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int)) 
           (=> (and (= xs (cons x ys)) (length ys l)) (length xs (+ l 1)))))

(declare-fun remove (Lst Int Lst) Bool)

(assert (forall ((x Int)) (remove nil x nil)))
(assert (forall ((x Int) (xs Lst) (ys Lst)) 
	(=> (= xs (cons x ys)) (remove xs x ys))))
(assert (forall ((x Int) (xs Lst) (n Int) (ys Lst) (zs Lst)) 
	(=> (and (= xs (cons x ys)) (remove ys n zs)) (remove xs n zs))))

(declare-fun contains (Lst Int Bool) Bool)
(assert (forall ((x Int)) (contains nil x false)))
(assert (forall ((x Int) (xs Lst)) (contains (cons x xs) x true)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (n Int) (r Bool))
	(=> (and (= xs (cons x ys)) (contains ys n r)) (contains xs n r))))

(assert (forall ((n Int) (xs Lst) (ys Lst) (l1 Int) (l2 Int))
       (=> (and (contains xs n true) (remove xs n ys) (length xs l1) (length ys l2) 
       	(not (= l1 l2))) false)))
(check-sat)
