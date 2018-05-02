(define-sort door () Int)





(declare-const Guest_d door)
(declare-const Guest_d_done Bool)


(declare-const Host_goat door)
(declare-const Host_goat_done Bool)

(assert (not (= Host_goat Guest_d)))
(declare-const Guest_switch Bool)
(declare-const Guest_switch_done Bool)


(declare-const Host_car door)
(declare-const Host_car_done Bool)

(assert (not (= Host_goat Host_car)))
(declare-const Guest_outcome Int)
(assert (= Guest_outcome (ite (and Host_car_done Guest_switch_done) (ite (iff (not (= Guest_d Host_car)) Guest_switch) 20 (- 20)) (ite (not Host_car_done) 20 (- 100)))))
(declare-const Host_outcome Int)
(assert (= Host_outcome (ite (and Host_car_done Guest_switch_done) 0 (ite (not Host_car_done) (- 100) 0))))

(check-sat)
(get-model)