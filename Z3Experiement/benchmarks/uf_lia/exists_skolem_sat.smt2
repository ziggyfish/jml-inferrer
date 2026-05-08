(set-info :status sat)
(set-logic UFLIA)
(assert (exists ((x Int)) (and (>= x 0) (<= x 100))))
(check-sat)
