(set-info :status sat)
(set-logic QF_BV)
(assert (= (bvshl #b0001 #b0011) #b1000))
(check-sat)
