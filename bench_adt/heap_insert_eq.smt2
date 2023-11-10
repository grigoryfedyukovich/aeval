(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-datatypes () ((Heap (hleaf) (heap (rk Int) (value Int) (hleft Heap) (hright Heap)))))
(declare-fun rightHeight (Heap) Int)
(assert (= (rightHeight hleaf) 0))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap)) (= (rightHeight (heap k v l r)) (+ 1 (rightHeight r)))))

(declare-fun rank (Heap) Int)
(assert (= (rank hleaf) 0))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap)) (= (rank (heap k v l r)) k)))

(declare-fun hasLeftistProperty (Heap) Bool)
(assert (hasLeftistProperty hleaf))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap))
    (= (hasLeftistProperty (heap k v l r))
    (and (hasLeftistProperty l) (hasLeftistProperty r)
    (<= (rightHeight r) (rightHeight l))
    (= k (+ 1 (rightHeight r)))))))

(declare-fun hsize (Heap) Int)
(assert (= (hsize hleaf) 0))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap)) (= (hsize (heap k v l r)) (+ 1 (+ (hsize l) (hsize r))))))

(declare-fun mergea (Int Heap Heap) Heap)
(assert (forall ((v Int) (l Heap) (r Heap))
    (= (mergea v l r) (ite (<= (rank r) (rank l)) (heap (+ 1 (rank r)) v l r) (heap (+ 1 (rank l)) v r l)))))

(declare-fun merge (Heap Heap) Heap)
(assert (forall ((h Heap)) (= (merge h hleaf) h)))
(assert (forall ((h Heap)) (= (merge hleaf h) h)))
(assert (forall ((k1 Int) (v1 Int) (l1 Heap) (r1 Heap) (k2 Int) (v2 Int) (l2 Heap) (r2 Heap))
    (= (merge (heap k1 v1 l1 r1) (heap k2 v2 l2 r2))
    (ite (< v2 v1) (mergea v1 l1 (merge r1 (heap k2 v2 l2 r2)))
    (mergea v2 l2 (merge (heap k1 v1 l1 r1) r2))))))

(declare-fun hinsert (Heap Int) Heap)
(assert (forall ((h Heap) (n Int)) (= (hinsert h n) (merge (heap 1 n hleaf hleaf) h))))

; extra lemmas
(assert (forall ((x Heap)) (>= (hsize x) 0)))

(assert (not (forall ((x Heap) (n Int)) (=> (hasLeftistProperty x) (hasLeftistProperty (hinsert x n))))))
(check-sat)
