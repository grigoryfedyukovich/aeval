(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst Lst) Bool)
(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst)) 
	(=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))

(declare-fun rev (Lst Lst) Bool)
(assert (rev nil nil))
(assert (forall ((xs Lst) (x Int) (ys Lst) (rs Lst) (ts Lst)) 
	(=> (and (= xs (cons x ys)) (rev ys rs) (append rs (cons x nil) ts)) (rev xs ts))))

; extra lemmas
(assert (forall ((xs Lst) (ys Lst)) (append xs nil xs)))
(assert (forall ((xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst) (us Lst))
	(=> (and (append xs ys rs) (append ys zs ts) (append xs ts us)) (append rs zs us))))

(assert (forall ((xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst) (us Lst) (ws Lst)) 
	(=> (and (append xs ys zs) (rev zs rs) (rev ys ts) (rev xs us) (append ts us ws) (not (= rs ws))) false)))

(check-sat)