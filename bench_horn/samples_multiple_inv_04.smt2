(declare-rel FUN (Int))
(declare-rel SAD (Int))
(declare-rel WEE (Int))
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

(rule (=> (SAD m) (WEE m)))

(rule (=>
    (and
	(WEE m)
	(= m1 (+ m 3))
    )
    (WEE m1)
  )
)

(rule (=> (and (WEE m) (not (>= m 30))) fail))

(query fail :print-certificate true)