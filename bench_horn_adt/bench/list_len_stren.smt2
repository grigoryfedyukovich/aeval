(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun length (Lst Int) Bool)
(declare-fun length_str (Lst Int) Bool)

(assert (length nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int)) 
           (=> (and (= xs (cons x ys)) (length ys l)) (length xs (+ l 1)))))

(assert (length_str nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l1 Int) (l2 Int))
           (=> (and (= xs (cons x ys)) (length ys l1) (length_str ys l2)) (length_str xs (+ l1 l2)))))

(assert (forall ((l Int) (xs Lst))
       (=> (and (length_str xs l) (not (>= l 0))) false)))

(check-sat)
