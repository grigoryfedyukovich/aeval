(declare-var i Int)
(declare-var i_ Int)
(declare-var LRG Int)
(declare-rel itp (Int Int))
(declare-rel fail ())

(rule (=>
  (= i 0)
  (itp i LRG)
))

(rule (=>
  (and
    (itp i_ LRG)
    (< i_ LRG)
    (= i (+ 1 i_))
  )
  (itp i LRG)
))

(rule (=>
  (and
    (itp LRG LRG)
    (> LRG 10000)   ; assume LRG is actually large (not asserted in the .c)
  ) fail))

(query fail :print-certificate true)

; int main() {
;     int i;
;     for (i = 0; i < LARGE_INT; i++) ;
;     __VERIFIER_assert(i == LARGE_INT);
;     return 0;
; }
