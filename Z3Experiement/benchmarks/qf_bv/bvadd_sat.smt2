(set-info :status sat)
(set-logic QF_BV)
(assert (= (bvadd #b00000001 #b00000001) #b00000010))
(check-sat)
