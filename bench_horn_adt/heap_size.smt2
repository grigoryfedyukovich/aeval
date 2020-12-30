(set-logic HORN)
(declare-datatypes () ((Heap (hleaf) (heap (rk Int) (value Int) (hleft Heap) (hright Heap)))))
(declare-fun hsize (Heap Int) Bool)

(assert (hsize hleaf 0))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap) (m Heap) (sl Int) (sr Int))
           (=> (and (= m (heap k v l r)) (hsize l sl) (hsize r sr)) (hsize m (+ 1 (+ sl sr))))))

(assert (forall ((s Int) (m Heap))
       (=> (and (hsize m s) (not (>= s 0))) false)))
(check-sat)
