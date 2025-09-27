

(declare-const Odd_c Bool)
(declare-const Odd_c_done Bool)



(declare-const Even_c Bool)
(declare-const Even_c_done Bool)


(declare-const Even_outcome Int)
(assert (= Even_outcome (ite (and Even_c_done Odd_c_done) (ite (iff Even_c Odd_c) 10 (- 10)) (ite (and (not Even_c_done) Odd_c_done) (- 100) (- 100)))))
(declare-const Odd_outcome Int)
(assert (= Odd_outcome (ite (and Even_c_done Odd_c_done) (ite (iff Even_c Odd_c) (- 10) 10) (ite (and (not Even_c_done) Odd_c_done) 10 (- 100)))))

(check-sat)
(get-model)