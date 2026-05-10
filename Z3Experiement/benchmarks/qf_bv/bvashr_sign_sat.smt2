(set-info :status sat)
(set-logic QF_BV)
(assert (= (bvashr #b1111 #b0001) #b1111))
(check-sat)
