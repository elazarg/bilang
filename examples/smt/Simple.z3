





(declare-const B_c Bool)
(declare-const B_c_done Bool)


(declare-const A_c Bool)
(declare-const A_c_done Bool)


(declare-const A_outcome Int)
(assert (= A_outcome (ite (or (not (= A_c B_c)) (not B_c_done)) 1 (- 1))))
(declare-const B_outcome Int)
(assert (= B_outcome (ite (or (= A_c B_c) (not A_c_done)) 1 (- 1))))

(check-sat)
(get-model)