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

(declare-fun hasLeftistProperty (Heap) Bool)
(assert (hasLeftistProperty hleaf))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap) (rh Int) (lh Int)) 
	(=> (and (hasLeftistProperty l) (hasLeftistProperty r) (rightHeight r rh) (rightHeight l lh)
		(<= rh lh) (= k (+ 1 rh))) (hasLeftistProperty (heap k v l r)))))
                                                                                               
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
                                                                                                      
(declare-fun hinsert (Heap Int Heap) Bool)
(assert (forall ((h Heap) (n Int) (h1 Heap))
	(=> (merge (heap 1 n hleaf hleaf) h h1) (hinsert h n h1))))                                                                                                  

(declare-fun hinsert-all (Lst Heap Heap) Bool)
(assert (forall ((h Heap)) (hinsert-all nil h h)))
(assert (forall ((h Heap) (n Int) (l Lst) (h1 Heap) (h2 Heap))
	(=> (and (hinsert-all l h h1) (hinsert h1 n h2)) (hinsert-all (cons n l) h h2))))

; conjecture
(assert (forall ((l Lst) (h Heap))
	(=> (and (hinsert-all l hleaf h) (not (hasLeftistProperty h))) false))); G-heap-5 
(check-sat)
