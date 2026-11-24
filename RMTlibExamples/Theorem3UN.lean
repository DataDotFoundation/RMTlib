import RMTlib.Moments.Theorem3UNLow

/-!
# Theorem 3 of Dehaye for U(N): checks and examples

Exact checks in `ℚ` of `RMT.UN.Theorem3` (through `thm3CoeffFast = thm3Coeff`,
`RMT.UN.thm3CoeffFast_eq`), against the coefficients of `∏_{i,j ≤ k} (N + i + j − 1)/(i + j − 1)`.
These are the numbers of `scripts/un_test.py` (variant `transpose`).
-/

open RMT RMT.UN

-- The kernel `g(u) = u/(1 − e^{−u})`: `1, 1/2, 1/12, 0, −1/720, …` (`g_n = B⁺_n/n!`).
#guard (List.range 7).map gCoeff == [1, 1/2, 1/12, 0, -1/720, 0, 1/30240]

-- `k = 2`: `P_2(N) = (N⁴ + 8N³ + 23N² + 28N + 12)/12`; Theorem 3 gives every coefficient.
#guard
  let t := (List.range 5).map (thm3CoeffFast 2)
  t == [1/12, 2/3, 23/12, 7/3, 1] && t == (List.range 5).map (exactCoeff 2)

-- `k = 3`: the coefficients of `P_3(N)`, from `N⁹` down to `N⁰`; Theorem 3 gives every one.
#guard
  let t := (List.range 10).map (thm3CoeffFast 3)
  t == [1/8640, 1/320, 53/1440, 119/480, 1009/960, 929/320, 5629/1080, 1403/240, 37/10, 1] &&
    t == (List.range 10).map (exactCoeff 3)

-- `k ≤ 1`.
#guard (List.range 2).all fun k => (List.range (k * k + 1)).all fun M =>
  thm3CoeffFast k M == exactCoeff k M

-- `k = 4`, `M ≤ 4`, and `k = 5`, `M ≤ 2`.
#guard (List.range 5).all fun M => thm3CoeffFast 4 M == exactCoeff 4 M
#guard (List.range 3).all fun M => thm3CoeffFast 5 M == exactCoeff 5 M

/-- Theorem 3 with the *untransposed* rotated complement in place of `S_k(κ)`. -/
def rotCoeff (k M : ℕ) : ℚ :=
  let T := prodCoefMemo (gLookup (gTable (k * k)).reverse) (memoKeys k M) (cells k)
  let rot : (Fin k → ℕ) → Fin k → ℕ := fun κ i => k - κ (Fin.rev i)
  1 / ((k * k - M).factorial : ℚ) * ∑ m ∈ Finset.range (M + 1),
    ∑ κ ∈ boxParts k m, ∑ lam ∈ boxParts k (M - m),
      dCoef (fun α β => T.get (α, β)) κ lam * (skewDim lam (k * k - m - (M - m)) (rot κ) : ℚ)

-- With the untransposed complement only the leading terms agree (as `un_test.py` found):
-- `M ≤ 3`, and it fails from `M = 4` on, for `k = 2` and `k = 3`.
#guard (List.range 5).map (fun M => rotCoeff 2 M == exactCoeff 2 M) ==
  [true, true, true, true, false]
#guard (List.range 10).map (fun M => rotCoeff 3 M == exactCoeff 3 M) ==
  [true, true, true, true, false, false, false, false, false, false]

/-- The proved cases, for every `k`. -/
example (k : ℕ) : thm3Coeff k 0 = (momentPoly k).coeff (k * k) := theorem3_zero k
example (k : ℕ) (hk : 1 ≤ k) : thm3Coeff k 1 = (momentPoly k).coeff (k * k - 1) :=
  theorem3_one k hk
example (k : ℕ) : thm3Coeff k 0 = ksConst k := thm3Coeff_zero k
