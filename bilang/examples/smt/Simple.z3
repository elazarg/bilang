


(assert true)




(assert true)

(declare-const A_c Bool)
(declare-const A_c_done Bool)

(assert true)

(declare-const B_c Bool)
(declare-const B_c_done Bool)

(assert true)

(declare-const A_c Bool)
(declare-const A_c_done Bool)

(assert true)

(assert (= A_outcome (ite (or (<> A_c B_c) (not B_c_done)) 1 (- 1))))
(assert (= B_outcome (ite (or (= A_c B_c) (not A_c_done)) 1 (- 1))))