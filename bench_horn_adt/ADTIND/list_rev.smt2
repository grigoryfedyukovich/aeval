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
(assert (forall ((xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst) (us Lst) (ws Lst))
       (=> (and (append ys zs rs) (append xs ys ts) (append xs rs us) (append ts zs ws) (not (= us ws))) false)))
(assert (forall ((xs Lst) (ys Lst)) (=> (and (append xs nil ys) (not (= xs ys))) false)))
(assert (forall ((xs Lst) (ys Lst) (zs Lst) (us Lst) (rs Lst) (ts Lst) (vs Lst))
    (=> (and (append xs ys zs) (rev ys rs) (rev xs ts) (append rs ts us) (rev zs vs) (not (= us vs))) false)))

(assert (forall ((xs Lst) (ys Lst) (zs Lst)) (=> (and (rev xs ys) (rev ys zs) (not (= xs zs))) false)))

(check-sat)
(assert (forall ((x Int) (y Int)) (=> (> x y) (max x y x))))