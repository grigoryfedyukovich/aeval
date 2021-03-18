(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Queue (queue (front Lst) (back Lst)))))

(declare-fun len (Lst Int) Bool)
(assert (len nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int)) 
           (=> (and (= xs (cons x ys)) (len ys l)) (len xs (+ l 1)))))

(declare-fun qlen (Queue Int) Bool)
(assert (forall ((x Lst) (y Lst) (lx Int) (ly Int) (lq Int)) 
	(=> (and (len x lx) (len y ly)) (qlen (queue x y) (+ lx ly)))))

(declare-fun append (Lst Lst Lst) Bool)
(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst)) 
	(=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))


(declare-fun butlast (Lst Lst) Bool)
(assert (butlast nil nil))
(assert (forall ((n Int) (x Lst) (y Lst) (z Lst)) 
	(=> (and (butlast x y) (= z (ite (= x nil) nil (cons n y)))) (butlast (cons n x) z))))

(declare-fun qpopback (Queue Queue) Bool)
(assert (forall ((x Lst) (y Lst) (n Int)) (qpopback (queue x (cons n y)) (queue x y))))
(assert (forall ((x Lst) (y Lst)) (=> (butlast x y) (qpopback (queue x nil) (queue y nil)))))

(declare-fun isAmortized (Queue Bool) Bool)
(assert (forall ((x Lst) (y Lst) (lx Int) (ly Int)) 
	(=> (and (len x lx) (len y ly) (<= ly lx)) (isAmortized (queue x y) true))))

(declare-fun isNotEmpty (Queue Bool) Bool)
(assert (forall ((x Lst) (y Lst) (n Int) (z Lst)) (=> (= x (cons n y)) (isNotEmpty (queue x z) true))))
(assert (forall ((x Lst) (y Lst) (n Int) (z Lst)) (=> (= z (cons n y)) (isNotEmpty (queue x z) true))))

; extra lemma
(assert (forall ((x Lst) (n Int) (y Lst) (lx Int) (ly Int)) 
	(=> (and (butlast (cons n x) y)) (len y ly) (len x lx) (= lx ly))))

(assert (forall ((q Queue) (n Int) (p Queue) (lp Int) (lq Int)) 
	(=> (and (isNotEmpty q true) (isAmortized q true) (qpopback q p) (qlen p lp) (qlen q lq) 
		(not (= (+ 1 lp) lq))) false)))
(check-sat)
