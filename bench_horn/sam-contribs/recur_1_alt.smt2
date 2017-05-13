(declare-rel itp1 (Int Int))
(declare-rel fail ())

(declare-var cnt_all_1 Int)
(declare-var cnt_all_2 Int)
(declare-var st_all_1 Int)
(declare-var st_all_2 Int)

(declare-var segm1 Int)
(declare-var segm2 Int)

(declare-var m Int)



(rule (=> (and (= cnt_all_1 0) (= st_all_1 0))
      (itp1  cnt_all_1  st_all_1)))


(rule (=>
    (and
        (itp1 cnt_all_1 st_all_1)

          (or (and (= m 1) (= cnt_all_2 (+ 1 cnt_all_1)))
              (and (not (= m 1)) (= cnt_all_2 cnt_all_1)))

        (= st_all_2 (+ st_all_1 1))
    )
    (itp1 cnt_all_2 st_all_2 )
  )
)

(rule (=> (and (itp1 cnt_all_1 st_all_1 )

        (not (<= cnt_all_1 st_all_1))) fail))


(query fail :print-certificate true)
