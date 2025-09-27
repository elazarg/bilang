(define-sort options () Int)

(declare-const Gambler_bet options)
(declare-const Gambler_bet_done Bool)


(declare-const Race_winner options)
(declare-const Race_winner_done Bool)


(declare-const Gambler_outcome Int)
(assert (= Gambler_outcome (ite (or (not Race_winner_done) (= Race_winner Gambler_bet)) 100 0)))
(declare-const Race_outcome Int)
(assert (= Race_outcome (ite (or (not Race_winner_done) (= Race_winner Gambler_bet)) 0 100)))

(check-sat)
(get-model)