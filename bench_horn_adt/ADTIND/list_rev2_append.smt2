(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-fun append (Lst Lst Lst) Bool)

(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst)) 
	(=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))

(declare-fun rev2 (Lst Lst Lst) Bool)
(assert (forall ((a Lst)) (rev2 nil a a)))
(assert (forall ((x Int) (ts Lst) (xs Lst) (zs Lst) (rs Lst) (us Lst))
	(=> (and (= xs (cons x ts)) (= rs (cons x zs)) (rev2 ts rs us)) (rev2 xs zs us)))) 

; extra lemma
; (assert (forall ((xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst) (us Lst) (vs Lst))
; 	(=> (and (append xs ys rs) (append ys zs ts) (append xs ts us) (append rs zs vs) (not (= us vs))) false)))


(assert (forall ((xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst) (us Lst))
	(=> (and (append xs ys rs) (append ys zs ts) (append xs ts us)) (append rs zs us))))

(assert (forall ((xs Lst) (zs Lst) (ts Lst) (us Lst) (ys Lst)) 
	(=> (and (rev2 xs zs ts) (rev2 xs nil ys) (append ys zs us) (not (= ts us))) false)))

(check-sat)
