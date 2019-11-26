(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)
(declare-fun in3 () Elem)
(declare-fun out () Elem)
(declare-fun out2 () Elem)

; isempty

(assert (= xs nil))

; push

(assert (= xs1 (cons in3 (cons in xs))))

; pop

(assert (= xs (cons out2 (cons out xs1))))
