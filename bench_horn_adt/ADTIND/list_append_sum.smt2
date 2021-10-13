(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst Lst) Bool)

(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst)) 
  (=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))

(declare-fun sum (Lst Int) Bool)
(assert (sum nil 0))
(assert (forall ((x Int) (y Lst) (z Int)) 
	(=> (sum y z) (sum (cons x y) (+ x z)))))

(assert (forall ((x Lst) (y Lst) (z Lst) (r Int) (s Int) (t Int))
  (=> (and (append x y z) (sum x r) (sum y s) (sum z t) (not (= t (+ r s)))) false)))

(check-sat)