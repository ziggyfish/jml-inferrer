; 3 pigeons, 2 holes — UNSAT.
(set-logic QF_UF)
(declare-const p1h1 Bool) (declare-const p1h2 Bool)
(declare-const p2h1 Bool) (declare-const p2h2 Bool)
(declare-const p3h1 Bool) (declare-const p3h2 Bool)
; each pigeon in some hole
(assert (or p1h1 p1h2))
(assert (or p2h1 p2h2))
(assert (or p3h1 p3h2))
; no hole holds two pigeons
(assert (not (and p1h1 p2h1)))
(assert (not (and p1h1 p3h1)))
(assert (not (and p2h1 p3h1)))
(assert (not (and p1h2 p2h2)))
(assert (not (and p1h2 p3h2)))
(assert (not (and p2h2 p3h2)))
(check-sat)
