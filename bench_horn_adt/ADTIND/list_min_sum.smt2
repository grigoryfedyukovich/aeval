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

(assert (forall ((x Int) (y Int) (xs Lst))
       (=> (and (min xs x) (sum xs y) (>= x 0) (not (>= y 0))) false)))
(check-sat)