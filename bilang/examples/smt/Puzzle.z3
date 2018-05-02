

(declare-const Q_x Int)
(declare-const Q_x_done Bool)


(declare-const A_p Int)
(declare-const A_q Int)
(declare-const A_p_done Bool)
(declare-const A_q_done Bool)

(assert (and (and (= (* A_p A_q) Q_x) (not (= A_p 1))) (not (= A_q 1))))
(declare-const Q_outcome Int)
(assert (= Q_outcome 0))
(declare-const A_outcome Int)
(assert (= A_outcome 50))

(check-sat)
(get-model)