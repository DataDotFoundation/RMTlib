import RMTlib.Tableaux.JacobiTrudi

/-! `h_k(1^n)` values, and the Gelfand–Tsetlin counts that `jacobiTrudiOne` equals. -/

#guard RMT.hOne 3 2 == 6
#guard RMT.hOne 3 (-1) == 0
#guard RMT.hOne 1 5 == 1
#guard RMT.gtCount 3 (![2, 1, 0] : Fin 3 → ℕ) == 8

example : RMT.jacobiTrudiOne 3 ![2, 1, 0] = 8 := by
  rw [RMT.jacobiTrudiOne_eq_gtCount 3 _ (by decide)]
  norm_num [show RMT.gtCount 3 (![2, 1, 0] : Fin 3 → ℕ) = 8 by decide]
