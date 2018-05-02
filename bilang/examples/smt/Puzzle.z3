(declare-const Q_x Int)
(declare-const Q_x_done Bool)

(assert true)

(declare-const A_p Int)
(declare-const A_q Int)
(declare-const A_p_done Bool)
(declare-const A_q_done Bool)

(assert (and (and (= (* A_p A_q) Q_x) (<> A_p 1)) (<> A_q 1)))

(assert (= Q_outcome 0))
(assert (= A_outcome 50))