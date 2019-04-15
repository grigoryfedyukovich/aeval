(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Bin (One) (ZeroAnd (ZeroAnd_0 Bin)) (OneAnd (OneAnd_0 Bin)))))
(declare-fun s (Bin) Bin)
(declare-fun plus2 (Nat Nat) Nat)
(declare-fun toNat (Bin) Nat)
(declare-fun plus (Bin Bin) Bin)
(assert
  (not
    (forall ((x Bin) (y Bin))
      (= (toNat (plus x y)) (plus2 (toNat x) (toNat y))))))
(assert
  (forall ((x Bin))
    (= (s x)
      (ite
        (is-OneAnd x) (ZeroAnd (s (OneAnd_0 x)))
        (ite (is-ZeroAnd x) (OneAnd (ZeroAnd_0 x)) (ZeroAnd One))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus2 x y) (ite (is-S x) (S (plus2 (p x) y)) y))))
(assert
  (forall ((x Bin))
    (= (toNat x)
      (ite
        (is-OneAnd x) (S (plus2 (toNat (OneAnd_0 x)) (toNat (OneAnd_0 x))))
        (ite
          (is-ZeroAnd x) (plus2 (toNat (ZeroAnd_0 x)) (toNat (ZeroAnd_0 x)))
          (S Z))))))
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
