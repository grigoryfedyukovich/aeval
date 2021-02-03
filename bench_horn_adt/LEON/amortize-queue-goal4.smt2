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

;queues
(declare-datatypes () ((Queue (queue (front Lst) (back Lst)))))

(declare-fun qlen (Queue Int) Bool)
(assert (forall ((x Lst) (y Lst) (lx Int) (ly Int) (lq Int))
	(=> (and (len x lx) (len y ly)) (qlen (queue x y) (+ lx ly)))))

; conjecture
(assert (forall ((x Lst) (lx Int) (y Lst) (ly Int) (lq Int))
       (=> (and (len x lx) (len y ly) (qlen (queue x y) lq) (not (= (+ lx ly) lq))) false))) ; G-amortize-queue-4 
(check-sat)
