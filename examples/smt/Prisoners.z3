

(declare-const A_c Bool)
(declare-const A_c_done Bool)



(declare-const B_c Bool)
(declare-const B_c_done Bool)


(declare-const A_outcome Int)
(assert (= A_outcome (ite (and A_c_done B_c_done) (ite (and A_c B_c) (- 2) (ite (and A_c (not B_c)) 0 (ite (and (not A_c) B_c) (- 3) (- 1)))) (ite (not A_c_done) (- 100) 10))))
(declare-const B_outcome Int)
(assert (= B_outcome (ite (and A_c_done B_c_done) (ite (and A_c B_c) (- 2) (ite (and A_c (not B_c)) (- 3) (ite (and (not A_c) B_c) 0 (- 1)))) (ite (not A_c_done) 10 (- 100)))))

(check-sat)
(get-model)