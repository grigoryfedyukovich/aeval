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
(assert (forall ((xs Lst) (ys Lst) (zs Lst) (us Lst) (rs Lst) (ts Lst)) 
	(=> (and (append xs ys zs) (rev ys rs) (rev xs ts) (append rs ts us)) (rev zs us))))

(assert (forall ((xs Lst) (ys Lst) (zs Lst)) (=> (and (rev xs ys) (rev ys zs) (not (= xs zs))) false)))

(check-sat)
