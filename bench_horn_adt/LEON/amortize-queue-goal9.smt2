(set-logic HORN)

; lists
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst Lst) Bool)
(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst))
    (=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))

(declare-fun len (Lst Int) Bool)
(assert (len nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int))
           (=> (and (= xs (cons x ys)) (len ys l)) (len xs (+ l 1)))))

(declare-fun butlast (Lst Lst) Bool)
(assert (butlast nil nil))
(assert (forall ((n Int) (xs Lst) (rs Lst) (ys Lst))
    (=> (and (= ys (cons n xs)) (= xs nil)) (butlast ys nil))))
(assert (forall ((n Int) (xs Lst) (rs Lst) (ys Lst) (x Int) (zs Lst))
	(=> (and (butlast xs rs) (= ys (cons n xs)) (= xs (cons x zs))) (butlast ys (cons n rs)))))

; proven
(assert (forall ((x Lst) (n Int) (y Lst) (l Int)) 
	(=> (and (butlast (cons n x) y) (len (cons n x) l)) (len y (+ l 1))))) ; G-amortize-queue-5 

; conjecture
(assert (forall ((x Lst) (y Lst) (z Lst) (r Lst) (u Lst) (v Lst) (n Int))
	(=> (and (append x (cons n y) z) (butlast (cons n y) r) (append x r u) (butlast z v) (not (= v u))) 
		false))) ; G-amortize-queue-9 

(check-sat)
