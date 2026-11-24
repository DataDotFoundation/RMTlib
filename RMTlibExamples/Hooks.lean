import RMTlib.Tableaux.Hooks

/-! Hook products for small shapes: `H(2,1) = 3`, `H(3^3) = 8640`, `H(4,3,1) = 576`
(so `f^(4,3,1) = 8!/576 = 70`). -/

#guard RMT.hookProd (![2, 1] : Fin 2 → ℕ) == 3
#guard RMT.hookProd (![3, 3, 3] : Fin 3 → ℕ) == 8640
#guard RMT.hookProd (![4, 3, 1] : Fin 3 → ℕ) == 576
#guard RMT.hookProd (![4, 3, 1, 0] : Fin 4 → ℕ) == 576
