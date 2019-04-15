(declare-sort sk_a 0)
(declare-datatypes () ((Nat (S (p Nat)) (Z))))
(declare-datatypes ()
  ((List2 (Cons (Cons_0 sk_a) (Cons_1 List2)) (Nil))))
(declare-fun take (Nat List2) List2)
(declare-fun minus (Nat Nat) Nat)
(declare-fun lt (Nat Nat) Bool)
(declare-fun mod2 (Nat Nat) Nat)
(declare-fun length (List2) Nat)
(declare-fun drop (Nat List2) List2)
(declare-fun append (List2 List2) List2)
(declare-fun rotate (Nat List2) List2)
(assert
  (not
    (forall ((n Nat) (xs List2))
      (= (rotate n xs)
        (append (drop (mod2 n (length xs)) xs)
          (take (mod2 n (length xs)) xs))))))
(assert
  (forall ((x Nat) (y List2))
    (= (take x y)
      (ite
        (is-Z x) Nil
        (ite (is-Nil y) Nil (Cons (Cons_0 y) (take (p x) (Cons_1 y))))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (minus x y)
      (ite (is-Z x) Z (ite (is-Z y) (S (p x)) (minus (p x) (p y)))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (lt x y)
      (ite (is-Z y) false (ite (is-Z x) true (lt (p x) (p y)))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (mod2 x y)
      (ite
        (is-Z y) Z
        (ite (lt x (S (p y))) x (mod2 (minus x (S (p y))) (S (p y))))))))
(assert
  (forall ((x List2))
    (= (length x) (ite (is-Nil x) Z (S (length (Cons_1 x)))))))
(assert
  (forall ((x Nat) (y List2))
    (= (drop x y)
      (ite (is-Z x) y (ite (is-Nil y) Nil (drop (p x) (Cons_1 y)))))))
(assert
  (forall ((x List2) (y List2))
    (= (append x y)
      (ite (is-Nil x) y (Cons (Cons_0 x) (append (Cons_1 x) y))))))
(assert
  (forall ((x Nat) (y List2))
    (= (rotate x y)
      (ite
        (is-Z x) y
        (ite
          (is-Nil y) Nil
          (rotate (p x) (append (Cons_1 y) (Cons (Cons_0 y) Nil))))))))
(check-sat)
