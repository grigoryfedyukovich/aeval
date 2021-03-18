(set-logic HORN)

; lists      
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

; heaps
(declare-datatypes () ((Heap (hleaf) (heap (rk Int) (value Int) (hleft Heap) (hright Heap)))))

(declare-fun rightHeight (Heap Int) Bool)
(assert (rightHeight hleaf 0))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap) (rh Int))
	(=> (rightHeight r rh) (rightHeight (heap k v l r) (+ 1 rh)))))

(declare-fun rank (Heap Int) Bool)
(assert (rank hleaf 0))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap))
	(rank (heap k v l r) k)))

(declare-fun hasLeftistProperty (Heap Bool) Bool)
(assert (hasLeftistProperty hleaf true))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap) (rh Int) (lh Int)) 
	(=> (and (hasLeftistProperty l true) (hasLeftistProperty r true) (rightHeight r rh) (rightHeight l lh)
		(<= rh lh) (= k (+ 1 rh))) (hasLeftistProperty (heap k v l r) true))))
                                                                                               
(declare-fun hsize (Heap Int) Bool)
(assert (hsize hleaf 0))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap) (lh Int) (rh Int))
	(=> (and (hsize l lh) (hsize r rh)) (hsize (heap k v l r) (+ 1 (+ lh rh))))))

(declare-fun mergea (Int Heap Heap Heap) Bool)
(assert (forall ((v Int) (l Heap) (r Heap) (rr Int) (lr Int))
	(=> (and (rank r rr) (rank l lr) (<= rr lr)) (mergea v l r (heap (+ rr 1) v l r)))))

(assert (forall ((v Int) (l Heap) (r Heap) (rr Int) (lr Int))
	(=> (and (rank r rr) (rank l lr) (> rr lr)) (mergea v l r (heap (+ lr 1) v r l)))))


(declare-fun merge (Heap Heap Heap) Bool)
(assert (forall ((h Heap)) (merge h hleaf h)))
(assert (forall ((h Heap)) (merge hleaf h h)))
(assert (forall ((k1 Int) (v1 Int) (l1 Heap) (r1 Heap) (k2 Int) (v2 Int) (l2 Heap) (r2 Heap) (h1 Heap) (h2 Heap))
	(=> (and (< v2 v1) (merge r1 (heap k2 v2 l2 r2) h1) (mergea v1 l1 h1 h2)) 
		(merge (heap k1 v1 l1 r1) (heap k2 v2 l2 r2) h2))))
(assert (forall ((k1 Int) (v1 Int) (l1 Heap) (r1 Heap) (k2 Int) (v2 Int) (l2 Heap) (r2 Heap) (h1 Heap) (h2 Heap))
	(=> (and (>= v2 v1) (merge (heap k1 v1 l1 r1) r2 h1) (mergea v2 l2 h1 h2)) 
		(merge (heap k1 v1 l1 r1) (heap k2 v2 l2 r2) h2))))

; conjecture
(assert (forall ((x Heap) (y Heap) (h Heap) (hs Int) (xs Int) (ys Int))
	(=> (and (hasLeftistProperty x true) (hasLeftistProperty y true) (merge x y h) (hsize h hs)
		(hsize x xs) (hsize y ys) (not (= hs (+ 10 (+ xs ys))))) false)))

(check-sat)
