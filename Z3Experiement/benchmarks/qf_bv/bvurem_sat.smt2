(set-info :status sat)
(set-logic QF_BV)
(assert (= (bvurem #b0111 #b0010) #b0001))
(check-sat)
