(declare-datatypes ()
  ((Bin (One) (ZeroAnd (ZeroAnd_0 Bin)) (OneAnd (OneAnd_0 Bin)))))
(declare-fun s (Bin) Bin)
(declare-fun plus (Bin Bin) Bin)
(assert
  (not
    (forall ((x Bin) (y Bin) (z Bin))
      (= (plus x (plus y z)) (plus (plus x y) z)))))
(assert
  (forall ((x Bin))
    (= (s x)
      (ite
        (is-OneAnd x) (ZeroAnd (s (OneAnd_0 x)))
        (ite (is-ZeroAnd x) (OneAnd (ZeroAnd_0 x)) (ZeroAnd One))))))
(assert
  (forall ((x Bin) (y Bin))
    (= (plus x y)
      (ite
        (is-OneAnd x)
        (ite
          (is-OneAnd y) (ZeroAnd (s (plus (OneAnd_0 x) (OneAnd_0 y))))
          (ite
            (is-ZeroAnd y) (OneAnd (plus (OneAnd_0 x) (ZeroAnd_0 y)))
            (s (OneAnd (OneAnd_0 x)))))
        (ite
          (is-ZeroAnd x)
          (ite
            (is-OneAnd y) (OneAnd (plus (ZeroAnd_0 x) (OneAnd_0 y)))
            (ite
              (is-ZeroAnd y) (ZeroAnd (plus (ZeroAnd_0 x) (ZeroAnd_0 y)))
              (s (ZeroAnd (ZeroAnd_0 x)))))
          (s y))))))
(check-sat)
