; synthèse d'invariant de programme
; on déclare le symbole non interprété de relation Invar
(declare-fun Invar (Int Int ) Bool)
; la relation Invar est un invariant de boucle
(assert (forall ((i Int)(v Int))
(=> (and (Invar i v) (< i 3)) (Invar (+ v 3) (+ i 1) ))))
; la relation Invar est vraie initialement
(assert (Invar 0 0))
; l'assertion finale est vérifiée
(assert (forall ((i Int)(v Int))
(=> (and (Invar i v) (>= i 3)) (= v 9))))
; appel au solveur
(check-sat-using (then qe smt))
(get-model)