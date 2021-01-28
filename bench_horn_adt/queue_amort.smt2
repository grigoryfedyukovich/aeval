(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Queue (queue (front Lst) (back Lst)))))

(declare-fun len (Lst Int) Bool)

(assert (len nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int)) 
           (=> (and (= xs (cons x ys)) (len ys l)) (len xs (+ l 1)))))

(declare-fun append (Lst Lst Lst) Bool)
(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst)) 
	(=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))


(declare-fun rev2 (Lst Lst Lst) Bool)
(assert (forall ((xs Lst)) (rev2 nil xs xs)))
(assert (forall ((x Int) (ts Lst) (xs Lst) (zs Lst) (rs Lst) (us Lst))
	(=> (and (= xs (cons x ts)) (= rs (cons x zs)) (rev2 ts rs us)) (rev2 xs zs us)))) 

(declare-fun qrev (Lst Lst) Bool)
(assert (forall ((xs Lst) (ys Lst)) (=> (rev2 xs nil ys) (qrev xs ys))))

(declare-fun amortizeQueue (Lst Lst Queue) Bool)
(assert (forall ((x Lst) (y Lst) (q Queue) (ly Int) (lx Int) (z Lst) (a Lst)) 
	(=> (and (len y ly) (len x lx) (qrev y z) (append x z a)
		(= q (ite (<= ly lx) (queue x y) (queue a nil)))) (amortizeQueue x y q))))

(declare-fun isAmortized (Queue) Bool)
(assert (forall ((x Lst) (y Lst) (lx Int) (ly Int)) 
	(=> (and (len x lx) (len y ly) (<= ly lx)) (isAmortized (queue x y)))))

; extra lemma
(assert (forall ((x Lst) (lx Int)) (=> (len x lx) (<= 0 lx))))

(assert (forall ((x Lst) (y Lst) (q Queue)) 
	(=> (and (amortizeQueue x y q) (not (isAmortized q))) false)))

(check-sat)