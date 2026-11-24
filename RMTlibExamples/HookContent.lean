import RMTlib.Tableaux.HookContent

/-! Gelfand–Tsetlin counts: `dim V_(2,1)(U(3)) = 8` (adjoint), `dim V_(2,2)(U(4)) = 20`,
`dim V_(1)(U(n)) = n`, and the `2 × 2` square for `U(3)`: `#SSYT = 6`. Each checked against
the hook-content product. -/

#guard RMT.gtCount 3 (![2, 1, 0] : Fin 3 → ℕ) == 8
#guard RMT.gtCount 4 (![2, 2, 0, 0] : Fin 4 → ℕ) == 20
#guard RMT.gtCount 5 (![1, 0, 0, 0, 0] : Fin 5 → ℕ) == 5
#guard RMT.gtCount 3 (![2, 2, 0] : Fin 3 → ℕ) == 6
#guard [(![2, 1, 0] : Fin 3 → ℕ), ![3, 1, 1], ![2, 2, 2], ![4, 2, 0], ![3, 3, 1]].all fun ν =>
  RMT.gtCount 3 ν * RMT.hookProd ν ==
    ∏ i : Fin 3, ∏ c ∈ Finset.range (ν i), (3 - (i : ℕ) + c)
