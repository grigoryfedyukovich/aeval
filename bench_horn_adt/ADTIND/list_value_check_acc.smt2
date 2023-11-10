;There is some weird error rn
(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-fun length (Lst Int) Bool)
(declare-fun ff () Bool)

;(assert (length nil 0))
(assert (forall ((x1 Int) (x2 Int) (xs Lst) (ys Lst) (zs Lst) (l Int))
       (=> (and (= xs (cons x1 ys)) (= ys (cons x2 zs)) (not (= (head (tail xs)) x2))) ff)))
(assert (not ff))
(check-sat)