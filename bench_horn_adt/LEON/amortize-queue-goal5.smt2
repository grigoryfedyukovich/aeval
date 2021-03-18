(set-logic HORN)

; lists
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

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

; conjecture
(assert (forall ((x Lst) (y Int) (z Lst) (ly Int) (lz Int)) 
	(=> (and (len (cons y x) ly) (butlast (cons y x) z) (len z lz) (not (= (+ lz 1) ly))) false)))
(check-sat)
