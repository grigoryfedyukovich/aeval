(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)
(declare-fun out () Elem)

; isempty

(assert (= xs nil))

; push

(assert (= xs1 (cons in xs)))

; pop

(assert (= xs (cons out xs1)))
