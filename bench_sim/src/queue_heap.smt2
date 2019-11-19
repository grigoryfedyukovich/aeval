(declare-sort Elem)
(declare-sort Ptr)

(declare-fun in () Elem)
(declare-fun out () Elem)

(declare-fun null () Ptr)

(declare-fun head  () Ptr)
(declare-fun head1 () Ptr)

(declare-fun alloc  () (Array Ptr Bool))
(declare-fun alloc1 () (Array Ptr Bool))
(declare-fun data   () (Array Ptr Elem))
(declare-fun data1  () (Array Ptr Elem))
(declare-fun next   () (Array Ptr Ptr))
(declare-fun next1  () (Array Ptr Ptr))

(declare-fun last  (Ptr (Array Ptr Ptr)) (Ptr))
;(assert (forall ((hd Ptr) (next (Array Ptr Ptr)))
;  (=> (and (distinct hd null) (select alloc hd))
;      (= (last hd H) (ite (= (select next hd) null) hd (last (select next hd)))))))

; isempty

(assert
  (= head null))

; enqueue

(assert
  (and
    (not (select alloc hd1))
    (distinct hd1 null)
    (= alloc1 (store alloc hd1))
    (= next1  (store next hd1 hd))
    (= data1  (store data hd1 in))))

; dequeue

(assert
  (and
    (= hd1 hd)
    (= next1  (store hd null))
    (= data1  data)
    (= alloc1 alloc)
    (= (out (data (last hd next))))))

