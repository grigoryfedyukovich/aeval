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

(declare-fun qreva (Lst Lst Lst) Bool)
(assert (forall ((x Lst)) (qreva nil x x)))
(assert (forall ((x Lst) (y Lst) (z Int) (u Lst))
    (=> (qreva x (cons z y) u) (qreva (cons z x) y u))))

; conjecture
(assert (forall ((x Lst) (y Lst) (z Lst) (lx Int) (ly Int) (lz Int)) 
	(=> (and (qreva x y z) (len z lz) (len x lx) (len y ly) (not (= lz (+ 1(+ lx ly))))) 
		false))) ; G-amortize-queue-2 
(check-sat)
