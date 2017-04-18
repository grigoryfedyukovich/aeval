(declare-rel itp1 (Int Int Int))

(declare-var x1 Int)
(declare-var y1 Int)
(declare-var z1 Int)
(declare-var x2 Int)
(declare-var y2 Int)
(declare-var z2 Int)

(declare-rel fail ())
(rule (=> (and (= x1 0) (= y1 0) (= z1 0)) (itp1 x1 y1 z1)))
; COUNTERs -> x and y (nondet choice)
(rule (=>
    (and
        (itp1 x1 y1 z1)
        (or
            (and (= x2 (+ x1 1)) (= y2 y1) (= z2 (+ z1 1)))
            (and (= y2 (+ y1 1)) (= x2 x1) (= z2 (- z1 1)))
	)
        ;(= x2 (+ y2 z2))             ; desired invariant
    )
    (itp1 x2 y2 z2)
  )
)

; the problem is assumption (= x1 y1) that does not hold after a single iter of the loop making the body unsatisfiable. 

(rule (=> (and (itp1 x1 y1 z1) (= x1 y1) (not (= z1 0))) fail))


(query fail :print-certificate true)


