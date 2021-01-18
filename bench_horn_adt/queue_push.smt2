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
(assert (forall ((as Lst)) (rev2 nil as as)))
(assert (forall ((x Int) (ts Lst) (xs Lst) (as Lst) (rs Lst) (us Lst))
	(=> (and (= xs (cons x ts)) (= rs (cons x as)) (rev2 ts rs us)) (rev2 xs as us)))) 

(declare-fun qrev (Lst Lst) Bool)
(assert (forall ((xs Lst) (ys Lst)) (=> (rev2 xs nil ys) (qrev xs ys))))

(declare-fun amortizeQueue (Lst Lst Queue) Bool)
(assert (forall ((x Lst) (y Lst) (q Queue) (ly Int) (lx Int) (z Lst) (a Lst)) 
	(=> (and (len y ly) (len x lx) (qrev y z) (append x z a)
		(= q (ite (<= ly lx) (queue x y) (queue a nil)))) (amortizeQueue x y q))))

(declare-fun qpush (Queue Int Queue) Bool)
(assert (forall ((x Lst) (y Lst) (n Int) (q Queue)) 
	(=> (amortizeQueue x (cons n y) q) (qpush (queue x y) n q))))

; extra lemma
(assert (forall ((x Lst) (y Lst) (q Queue) (lx Int) (ly Int) (lq Int)) 
	(=> (and (len x lx) (len y ly) (amortizeQueue x y q) (qlen q lq)) (= lq (+ lx ly)))))

(assert (forall ((q Queue) (n Int) (p Queue) (lp Int) (lq Int)) 
	(=> (and (qpush q n p) (qlen p lp) (qlen q lq) (not (= lp (+ 1 lq)))) false)))
(check-sat)
