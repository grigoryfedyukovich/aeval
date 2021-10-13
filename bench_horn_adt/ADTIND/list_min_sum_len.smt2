(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun min (Lst Int) Bool)
(assert (min nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int) (r Int)) 
           (=> (and (= xs (cons x ys)) (min ys l) (= r (ite (< l x) l x))) (min xs r))))

(declare-fun sum (Lst Int) Bool)
(assert (sum nil 0))
(assert (forall ((x Int) (y Lst) (z Int)) 
       (=> (sum y z) (sum (cons x y) (+ x z)))))


(declare-fun length (Lst Int) Bool)
(assert (length nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int)) 
           (=> (and (= xs (cons x ys)) (length ys l)) (length xs (+ l 1)))))

(assert (forall ((x Int) (s Int) (l Int) (xs Lst))
       (=> (and (min xs x) (sum xs s) (length xs l) (> x 0) (not (>= s l))) false)))
(check-sat)