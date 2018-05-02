(define-sort choice () Int)

(declare-const Issuer_c choice)
(declare-const Issuer_c_done Bool)



(declare-const Alice_c choice)
(declare-const Alice_c_done Bool)



(declare-const Bob_c choice)
(declare-const Bob_c_done Bool)


(declare-const Bob_outcome Int)
(assert (= Bob_outcome (ite (or (not Alice_c_done) (not Bob_c_done)) (- 10) (ite (not Issuer_c_done) (- 10) (ite (= Alice_c Bob_c) (- 10) (ite (= (* (/ (+ (+ Alice_c Bob_c) Issuer_c) 2) 2) (+ (+ Alice_c Bob_c) Issuer_c)) (- 10) 20))))))
(declare-const Issuer_outcome Int)
(assert (= Issuer_outcome (ite (or (not Alice_c_done) (not Bob_c_done)) 20 (ite (not Issuer_c_done) (- 10) (ite (= Alice_c Bob_c) 20 (ite (= (* (/ (+ (+ Alice_c Bob_c) Issuer_c) 2) 2) (+ (+ Alice_c Bob_c) Issuer_c)) (- 10) (- 10)))))))
(declare-const Alice_outcome Int)
(assert (= Alice_outcome (ite (or (not Alice_c_done) (not Bob_c_done)) (- 10) (ite (not Issuer_c_done) 20 (ite (= Alice_c Bob_c) (- 10) (ite (= (* (/ (+ (+ Alice_c Bob_c) Issuer_c) 2) 2) (+ (+ Alice_c Bob_c) Issuer_c)) 20 (- 10)))))))

(check-sat)
(get-model)