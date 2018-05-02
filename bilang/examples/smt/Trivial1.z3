

(declare-const A_outcome Int)
(assert (= A_outcome 0))

(check-sat)
(get-model)