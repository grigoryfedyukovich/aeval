(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun sum (Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun cubes (Nat) Nat)
(assert
  (not (forall ((n Nat)) (= (cubes n) (mult (sum n) (sum n))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat))
    (= (sum x) (ite (is-S x) (plus (sum (p x)) (S (p x))) Z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))
(assert
  (forall ((x Nat))
    (= (cubes x)
      (ite
        (is-S x)
        (plus (cubes (p x)) (mult (mult (S (p x)) (S (p x))) (S (p x))))
        Z))))
(check-sat)
