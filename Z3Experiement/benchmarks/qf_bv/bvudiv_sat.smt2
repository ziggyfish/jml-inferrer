(set-info :status sat)
(set-logic QF_BV)
(assert (= (bvudiv #b0110 #b0010) #b0011))
(check-sat)
