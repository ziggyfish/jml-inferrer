(set-info :status sat)
(set-logic QF_BV)
(assert (= (bvmul #b0011 #b0010) #b0110))
(check-sat)
