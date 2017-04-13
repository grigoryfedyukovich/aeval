(declare-rel FUN (Int))
(declare-rel SAD (Int))
(declare-var m Int)
(declare-var m1 Int)

(declare-rel fail ())

(rule (=>
    (> m 50) (FUN m)
  )
)

(rule (=> 
    (and 
	(FUN m)
	(= m1 (+ m 1))
    )
    (FUN m1)
  )
)

(rule (=> (FUN m) (SAD m)))

(rule (=> 
    (and 
	(SAD m)
	(= m1 (+ m 2))
    )
    (SAD m1)
  )
)

(rule (=> (and (SAD m) (not (>= m 30))) fail))

(query fail :print-certificate true)

