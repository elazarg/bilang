


(assert true)




(assert true)

(declare-const Host_car door)
(declare-const Host_car_done Bool)

(assert true)

(declare-const Guest_d door)
(declare-const Guest_d_done Bool)

(assert true)

(declare-const Host_goat door)
(declare-const Host_goat_done Bool)

(assert (<> Host_goat Guest_d))

(declare-const Guest_switch Bool)
(declare-const Guest_switch_done Bool)

(assert true)

(declare-const Host_car door)
(declare-const Host_car_done Bool)

(assert (<> Host_goat Host_car))

(assert (= Guest_outcome (ite (and (and (! (not Host_car_done)) (! (not Host_goat_done))) (! (not Guest_switch_done))) (ite (== (<> Guest_d Host_car) Guest_switch) 20 (- 20)) (ite (or (not Host_car_done) (not Host_goat_done)) 20 (- 100)))))
(assert (= Host_outcome (ite (and (and (! (not Host_car_done)) (! (not Host_goat_done))) (! (not Guest_switch_done))) 0 (ite (or (not Host_car_done) (not Host_goat_done)) (- 100) 0))))