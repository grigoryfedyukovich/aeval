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

(declare-fun qreva (Lst Lst Lst) Bool)
(assert (forall ((x Lst)) (qreva nil x x)))
(assert (forall ((x Lst) (y Lst) (z Int) (u Lst))
    (=> (qreva x (cons z y) u) (qreva (cons z x) y u))))

(declare-fun qrev (Lst Lst) Bool)
(assert (forall ((xs Lst) (ys Lst))
    (=> (qreva xs nil ys) (qrev xs ys))))

;queues
(declare-datatypes () ((Queue (queue (front Lst) (back Lst)))))

(declare-fun queue-to-lst (Queue Lst) Bool)
(assert (forall ((x Lst) (y Lst) (q Queue) (z Lst) (a Lst))
	(=> (and (qrev y z) (append x z a)) (queue-to-lst (queue x y) a))))

(declare-fun amortizeQueue (Lst Lst Queue) Bool)
(assert (forall ((x Lst) (y Lst) (q Queue) (ly Int) (lx Int) (z Lst) (a Lst)) 
	(=> (and (len y ly) (len x lx) (qrev y z) (append x z a)
		(= q (ite (<= ly lx) (queue x y) (queue a nil)))) (amortizeQueue x y q))))

(declare-fun qpop (Queue Queue) Bool)
(assert (forall ((x Lst) (y Lst) (n Int)) (qpop (queue x (cons n y)) (queue x y))))
(assert (forall ((x Lst) (y Lst)) (=> (butlast x y) (qpop (queue x nil) (queue y nil)))))

; conjecture
(assert (forall ((x Lst) (y Lst) (q Queue) (z Lst) (u Lst) (v Lst))
	(=> (and (queue-to-lst (queue x y) z) (butlast z u) (qpop (queue x y) q) (queue-to-lst q v) (not (= u v)))
		false))) ; G-amortize-queue-13 

(check-sat)
