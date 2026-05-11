(set-info :status sat)
(set-logic QF_BV)
(assert (= (bvsdiv #b1010 #b0010) #b1101))
(check-sat)
