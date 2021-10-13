(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst Lst) Bool)

(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst)) 
  (=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))

(declare-fun min (Lst Int) Bool)
(assert (min nil 0))
(assert (forall ((x Int) (y Lst) (z Int) (r Int)) 
  (=> (and (min y z) (= r (ite (< z x) z x))) (min (cons x y) r))))

(assert (forall ((x Lst) (y Lst) (z Lst) (r Int) (s Int) (t Int))
  (=> (and (append x y z) (min x r) (min y s) (min z t) (not (<= t r))) false)))

(check-sat)