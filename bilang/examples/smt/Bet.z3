


(assert true)

(declare-const Gambler_bet options)
(declare-const Gambler_bet_done Bool)

(assert true)

(declare-const Race_winner options)
(declare-const Race_winner_done Bool)

(assert true)

(assert (= Gambler_outcome (ite (or (not Race_winner_done) (= Race_winner Gambler_bet)) 100 0)))
(assert (= Race_outcome (ite (or (not Race_winner_done) (= Race_winner Gambler_bet)) 0 100)))