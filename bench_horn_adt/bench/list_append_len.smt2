(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-fun length (Lst Int) Bool)
(declare-fun append (Lst Lst Lst) Bool)

(assert (length nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int)) 
           (=> (and (= xs (cons x ys)) (length ys l)) (length xs (+ l 1)))))

(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst)) (=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))

(assert (forall ((xs Lst) (lx Int) (ys Lst) (ly Int) (zs Lst) (lz Int))
       (=> (and (length xs lx) (length ys ly) (append xs ys zs) (length zs lz) (not (= (+ lx ly) lz))) false)))
(check-sat)
