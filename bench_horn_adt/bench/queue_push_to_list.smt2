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

(declare-fun rev2 (Lst Lst Lst) Bool)
(assert (forall ((zs Lst)) (rev2 nil zs zs)))
(assert (forall ((x Int) (ts Lst) (xs Lst) (zs Lst) (rs Lst) (us Lst))
	(=> (and (= xs (cons x ts)) (= rs (cons x zs)) (rev2 ts rs us)) (rev2 xs zs us)))) 

(declare-fun qrev (Lst Lst) Bool)
(assert (forall ((xs Lst) (ys Lst)) 
	(=> (rev2 xs nil ys) (qrev xs ys))))

(declare-fun amortizeQueue (Lst Lst Queue) Bool)
(assert (forall ((x Lst) (y Lst) (q Queue) (ly Int) (lx Int) (z Lst) (a Lst)) 
	(=> (and (len y ly) (len x lx) (qrev y z) (append x z a)
		(= q (ite (<= ly lx) (queue x y) (queue a nil)))) (amortizeQueue x y q))))

(declare-fun qpush (Queue Int Queue) Bool)
(assert (forall ((x Lst) (y Lst) (n Int) (q Queue)) 
	(=> (amortizeQueue x (cons n y) q) (qpush (queue x y) n q))))


(declare-fun queue-to-lst (Queue Lst) Bool)
(assert (forall ((x Lst) (y Lst) (q Queue) (z Lst) (a Lst)) 
	(=> (and (qrev y z) (append x z a)) (queue-to-lst (queue x y) a))))
; extra lemmas
(assert (forall ((xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst) (us Lst))
	(=> (and (append xs ys rs) (append ys zs ts) (append xs ts us)) (append rs zs us))))
(assert (forall ((x Lst) (a Lst) (y Lst) (z Lst)) 
	(=> (and (rev2 x nil y) (append y a z)) (rev2 x a z))))
(assert (forall ((q Queue) (n Int) (x Lst) (y Lst) (p Queue) (z Lst)) 
	(=> (and (queue-to-lst q x) (append x (cons n nil) y) (qpush q n p) (queue-to-lst p z) (not (= y z))) 
		false)))

(check-sat)
