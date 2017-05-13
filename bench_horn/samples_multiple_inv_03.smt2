(declare-rel WRAP (Int))
(declare-rel NEST (Int))
(declare-rel WEEE (Int))
(declare-var m Int)
(declare-var m1 Int)

(declare-rel fail ())

(rule (=>
    (= m 0) (WRAP m)
  )
)


(rule (=> (WRAP m) (NEST m)))

(rule (=> (NEST m) (WEEE m)))

(rule (=> 
    (and 
	(WEEE m)
	(= m1 (+ m 1))
    )
    (WEEE m1)
  )
)

(rule (=> (WEEE m) (NEST m)))

(rule (=> (NEST m) (WRAP m)))

(rule (=> (and (WRAP m) (not (>= m 0))) fail))

(query fail :print-certificate true)

