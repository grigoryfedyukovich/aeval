(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-fun append (Lst Lst Lst) Bool)
(declare-fun rev2 (Lst Lst Lst) Bool)
(declare-fun len (Lst Int) Bool)

(assert (len nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int)) 
           (=> (and (= xs (cons x ys)) (len ys l)) (len xs (+ l 1)))))

(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst)) 
	(=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))

(assert (forall ((xs Lst)) (rev2 nil xs xs)))
(assert (forall ((xs Lst) (ys Lst) (zs Lst) (rs Lst) (x Int) (ts Lst)) 
	(=> (and (= xs (cons x ys)) (= zs (cons x ts)) (rev2 ys zs rs)) (rev2 xs ts rs))))

; extra lemmas
(assert (forall ((xs Lst) (ys Lst) (rs Lst) (zs Lst) ) 
	(=> (and (rev2 xs nil zs) (append zs ys rs)) (rev2 xs ys rs))))
(assert (forall ((xs Lst) (ys Lst) (zs Lst) (lx Int) (ly Int)) 
	(=> (and (append xs ys zs) (len xs lx) (len ys ly)) (len zs (+ lx ly)))))

(assert (forall ((xs Lst) (ys Lst) (lx Int) (ly Int)) 
	(=> (and (rev2 xs nil ys) (len xs lx) (len ys ly) (not (= lx ly))) false)))

(check-sat)
