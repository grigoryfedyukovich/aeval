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

(declare-fun length (Lst Int) Bool)
(assert (length nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int))
           (=> (and (= xs (cons x ys)) (length ys l)) (length xs (+ l 1)))))

(assert (forall ((xs Lst) (lx Int) (ys Lst) (ly Int) (zs Lst) (lz Int))
  (=> (and (length xs lx) (length ys ly) (append xs ys zs) (length zs lz) (not (= (+ lx ly) lz))) false)))

(assert (forall ((xs Lst) (lx Int) (ys Lst) (ly Int))
  (=> (and (length xs lx) (length ys ly) (rev xs ys) (not (= lx ly))) false)))


(check-sat)
