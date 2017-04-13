(declare-rel itp1 (Int Int))
(declare-rel fail ())

(declare-var cnt1 Int)
(declare-var cnt2 Int)
(declare-var cnt3 Int)
(declare-var cnt4 Int)
(declare-var cnt5 Int)
(declare-var cnt6 Int)

(declare-var pre1 Int)
(declare-var pre2 Int)
(declare-var pre3 Int)
(declare-var pre4 Int)
(declare-var pre5 Int)
(declare-var pre6 Int)

(declare-var pre_cnt_1 Int)
(declare-var pre_cnt_2 Int)
(declare-var pre_cnt_3 Int)
(declare-var pre_cnt_4 Int)
(declare-var pre_cnt_5 Int)
(declare-var pre_cnt_6 Int)

(declare-var st1 Int)
(declare-var st2 Int)
(declare-var st3 Int)
(declare-var st4 Int)
(declare-var st5 Int)
(declare-var st6 Int)

(declare-var cnt_all_1 Int)
(declare-var cnt_all_2 Int)
(declare-var st_all_1 Int)
(declare-var st_all_2 Int)

(declare-var segm1 Int)
(declare-var segm2 Int)

(declare-var m Int)




(define-fun rec1 ((m Int) (state1 Int) (state2 Int) (res1 Int) (res2 Int)) Bool

   (ite (and (= m 1) (= state1 0))
           (and (= state2 1) (= res2 res1))
           (ite (and (= m 2) (= state1 1))
                   (and (= state2 0) (= res2 (+ 1 res1)))
                   (and (= state2 state1) (= res2 res1))
        )
   )
)

(rule (=> (and (= cnt_all_1 0) (= st_all_1 0))
      (itp1  cnt_all_1  st_all_1)))


(rule (=>
    (and
        (itp1  cnt_all_1  st_all_1)


        (rec1 m st_all_1 st_all_2 cnt_all_1 cnt_all_2)
        

    )
    (itp1 cnt_all_2 st_all_2 )
  )
)

(rule (=> (and (itp1 cnt_all_1 st_all_1 )

        (not (and (>= cnt_all_1 0) (<= st_all_1 1)) )) fail))


(query fail :print-certificate true)

