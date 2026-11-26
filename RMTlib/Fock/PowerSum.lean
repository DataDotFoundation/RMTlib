import RMTlib.Fock.Laplacian

/-!
# The Fock adjoints of all power sums, on rows

For an `N × N` matrix of variables `X`, the Fock (Fischer) adjoint of multiplication by
`p_j(X) = tr(X^j)` is the differential operator `tr(∂^j)`, where `∂ = (∂/∂x_{ab})` is the matrix of
partial derivatives (`fischer_pX_mul`). On the row `h_k(X)` it removes a horizontal strip of `j`
boxes, weighted by `N + c` over the boxes removed:

  `tr(∂^j) h_{k+j}(X) = (N + k)(N + k + 1) ⋯ (N + k + j − 1) · h_k(X)`   (`trDp_hX`).

This is the content-weighted Murnaghan–Nakayama rule on rows: the only border strip of size `j`
in the row `(k + j)` is its last `j` boxes, of contents `k, …, k + j − 1` and height `0`. For
`j = 1` it is `RMT.Fock.trD_hX`. Consequently

  `⟨p_ρ(X), h_k(X)⟩_Fock = N (N + 1) ⋯ (N + k − 1) = w_∞^{(N)}((k))`   (`fischer_prod_pX_hX`)

for every composition `ρ` of `k`. In the content-twisted Hall pairing
`⟨p_ρ, s_λ⟩ = χ^λ(ρ) w_∞(λ)`, and `χ^{(k)} = 1`: the Fock pairing on rows is the twisted Hall
pairing against every power sum, not only against `p₁^k` (`RMT.Fock.fischer_trX_pow_sX`).

## The steps

* `pderiv_comm`: partial derivatives commute (their commutator is a derivation vanishing on the
  variables).
* `pathD n a b`: the entry `(∂^n)_{ab} = Σ_c ∂_{ac} (∂^{n-1})_{cb}`, the Fock adjoint of
  multiplication by `(X^n)_{ab}` (`fischer_pathX_mul`).
* `sqD_hX`: **`Σ_c ∂_{ac} ∂_{cb} h_{k+2}(X) = (N + k + 1) ∂_{ab} h_{k+1}(X)`**, by comparing
  coefficients. Adding `e_{ac} + e_{cb}` to `M` changes its row margin by `e_a + e_c`; summing the
  factor `α_c + 1` over `c` gives `|α| + N`.
* `pathD_hX`: `(∂^{n+1})_{ab} h_{k+n+1} = (N + k + 1) ⋯ (N + k + n) · ∂_{ab} h_{k+1}`, by
  iterating `sqD_hX`; the trace and `RMT.Fock.trD_hX` give `trDp_hX`.

The column `e_k(X)` should obey the `ω`-dual rule `tr(∂^j) e_{k+j} = (−1)^{j−1} ∏ (N − c) e_k`,
and every shape the full rule (checked numerically, `bridge/scripts/fock_power_sum_adjoints.py`); see
`bridge/links/fock-norm.md`.
-/

open MvPolynomial Finset

namespace RMT.Fock

/-! ## Partial derivatives commute -/

theorem pderiv_comm {σ : Type*} (i j : σ) (f : MvPolynomial σ ℚ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  have h : ⁅(pderiv i : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ)),
      (pderiv j : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply, zero_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) => D f) h
  simp only [Derivation.commutator_apply, zero_apply] at h2
  exact sub_eq_zero.mp h2

variable {N : ℕ}

/-! ## The matrix `∂^n` and its adjoint `X^n` -/

/-- The entry `(∂^n)_{ab}` of the `n`-th power of the matrix of partial derivatives
`∂ = (∂/∂x_{ab})`: `(∂^0)_{ab} = δ_{ab}`, `(∂^{n+1})_{ab} = Σ_c ∂_{ac} (∂^n)_{cb}`. -/
noncomputable def pathD : ℕ → Fin N → Fin N → MvPolynomial (Fin N × Fin N) ℚ →
    MvPolynomial (Fin N × Fin N) ℚ
  | 0, a, b, f => if a = b then f else 0
  | n + 1, a, b, f => ∑ c, pderiv (a, c) (pathD n c b f)

theorem pathD_zero (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    pathD 0 a b f = if a = b then f else 0 := rfl

theorem pathD_succ (n : ℕ) (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    pathD (n + 1) a b f = ∑ c, pderiv (a, c) (pathD n c b f) := rfl

/-- `(∂^n)_{ab}` commutes with every partial derivative. -/
theorem pathD_pderiv (n : ℕ) (a b : Fin N) (v : Fin N × Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    pathD n a b (pderiv v f) = pderiv v (pathD n a b f) := by
  induction n generalizing a with
  | zero => rw [pathD_zero, pathD_zero]; split_ifs <;> simp
  | succ n ih =>
    rw [pathD_succ, pathD_succ, map_sum]
    exact sum_congr rfl fun c _ => by rw [ih, pderiv_comm]

theorem pathD_one (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    pathD 1 a b f = pderiv (a, b) f := by
  rw [pathD_succ]
  simp only [pathD_zero, apply_ite (pderiv _), map_zero, sum_ite_eq', mem_univ, ite_true]

theorem fischer_zero_left {σ : Type*} (g : MvPolynomial σ ℚ) : fischer 0 g = 0 := by
  simp [fischer]

/-- `(X^{n+1})_{ab} = Σ_c x_{ac} (X^n)_{cb}`. -/
theorem genMat_pow_succ_apply (n : ℕ) (a b : Fin N) :
    (genMat N ^ (n + 1)) a b = ∑ c, X (a, c) * (genMat N ^ n) c b := by
  rw [pow_succ', Matrix.mul_apply]
  rfl

/-- **The Fock adjoint of multiplication by `(X^n)_{ab}` is `(∂^n)_{ab}`.** -/
theorem fischer_pathX_mul (n : ℕ) (a b : Fin N) (f g : MvPolynomial (Fin N × Fin N) ℚ) :
    fischer ((genMat N ^ n) a b * f) g = fischer f (pathD n a b g) := by
  classical
  induction n generalizing a f g with
  | zero =>
    rw [pow_zero, Matrix.one_apply, pathD_zero]
    split_ifs
    · rw [one_mul]
    · rw [zero_mul, fischer_zero_left, fischer_zero_right]
  | succ n ih =>
    rw [genMat_pow_succ_apply, sum_mul, fischer_sum_left, pathD_succ, fischer_sum_right]
    refine sum_congr rfl fun c _ => ?_
    rw [mul_assoc, fischer_X_mul_left, ih, pathD_pderiv]

variable (N) in
/-- The power sum `p_n(X) = tr(X^n)`. -/
noncomputable def pX (n : ℕ) : MvPolynomial (Fin N × Fin N) ℚ := ∑ a, (genMat N ^ n) a a

/-- The trace `tr(∂^n) = Σ_a (∂^n)_{aa}`, the Fock adjoint of `p_n(X)`. -/
noncomputable def trDp (n : ℕ) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    MvPolynomial (Fin N × Fin N) ℚ :=
  ∑ a, pathD n a a f

/-- **The Fock adjoint of multiplication by `p_n(X) = tr(X^n)` is `tr(∂^n)`.** -/
theorem fischer_pX_mul (n : ℕ) (f g : MvPolynomial (Fin N × Fin N) ℚ) :
    fischer (pX N n * f) g = fischer f (trDp n g) := by
  rw [pX, sum_mul, fischer_sum_left, trDp, fischer_sum_right]
  exact sum_congr rfl fun a _ => fischer_pathX_mul n a a f g

/-! ## Coefficient bookkeeping: one more unit at `(a, b)` -/

/-- `M` with one more unit at the entry `(a, b)`. -/
def addE (M : Fin N → Fin N → ℕ) (a b : Fin N) : Fin N → Fin N → ℕ :=
  fun i j => M i j + if i = a ∧ j = b then 1 else 0

theorem matExp_addE (M : Fin N → Fin N → ℕ) (a b : Fin N) :
    matExp (addE M a b) = matExp M + Finsupp.single (a, b) 1 := by
  ext ⟨i, j⟩
  simp only [matExp_apply, addE, Finsupp.add_apply, Finsupp.single_apply, Prod.ext_iff]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1.symm, h'.2.symm⟩]

theorem rowSum_addE (M : Fin N → Fin N → ℕ) (a b i : Fin N) :
    rowSum (addE M a b) i = rowSum M i + if i = a then 1 else 0 := by
  unfold rowSum addE
  rw [sum_add_distrib]
  congr 1
  by_cases hi : i = a
  · simp [hi]
  · simp [hi]

theorem colSum_addE (M : Fin N → Fin N → ℕ) (a b j : Fin N) :
    ∑ i, addE M a b i j = ∑ i, M i j + if j = b then 1 else 0 := by
  unfold addE
  rw [sum_add_distrib]
  congr 1
  by_cases hj : j = b
  · simp [hj]
  · simp [hj]

theorem prod_factorial_addE (M : Fin N → Fin N → ℕ) (a b : Fin N) :
    (∏ i, ∏ j, (addE M a b i j).factorial) = (M a b + 1) * ∏ i, ∏ j, (M i j).factorial := by
  have h : ∀ i, (∏ j, (addE M a b i j).factorial)
      = if i = a then (M a b + 1) * ∏ j, (M a j).factorial else ∏ j, (M i j).factorial := by
    intro i
    by_cases hi : i = a
    · subst hi
      rw [ite_eq_left rfl, ← prod_factorial_bump_vec]
      refine prod_congr rfl fun j _ => ?_
      by_cases hj : j = b <;> simp [addE, hj]
    · rw [ite_eq_right hi]
      refine prod_congr rfl fun j _ => ?_
      simp [addE, hi]
  simp_rw [h]
  rw [← mul_prod_erase univ _ (mem_univ a), ← mul_prod_erase univ
    (fun i => ∏ j, (M i j).factorial) (mem_univ a), ite_eq_left rfl, mul_assoc]
  congr 2
  exact prod_congr rfl fun i hi => ite_eq_right (ne_of_mem_erase hi)

theorem hCoeff_addE (α : Fin N → ℕ) (M : Fin N → Fin N → ℕ) (a b : Fin N) :
    hCoeff α (addE M a b) * ((M a b : ℚ) + 1) = hCoeff α M := by
  unfold hCoeff
  rw [prod_factorial_addE]
  have h1 : ((∏ i, ∏ j, (M i j).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have h2 : (M a b : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

theorem hCoeff_bumpVec (α : Fin N → ℕ) (M : Fin N → Fin N → ℕ) (c : Fin N) :
    hCoeff (fun i => α i + if i = c then 1 else 0) M = ((α c : ℚ) + 1) * hCoeff α M := by
  unfold hCoeff
  rw [prod_factorial_bump_vec]
  push_cast
  ring

theorem hCond_addE_addE (k : ℕ) (M : Fin N → Fin N → ℕ) (a b c : Fin N) :
    HCond (k + 2) (addE (addE M a c) c b) ↔ HCond (k + 1) (addE M a b) := by
  unfold HCond
  simp only [rowSum_addE, colSum_addE, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j => by have := h1 j; omega, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun j => by have := h1 j; omega, by omega⟩

/-! ## The square `∂²` on rows -/

/-- **`Σ_c ∂_{ac} ∂_{cb} h_{k+2}(X) = (N + k + 1) ∂_{ab} h_{k+1}(X)`**: the entry `(a, b)` of
`∂²` applied to a row is `N + k + 1` times the entry of `∂`. -/
theorem sqD_hX (k : ℕ) (a b : Fin N) :
    ∑ c, pderiv (a, c) (pderiv (c, b) (hX N (k + 2)))
      = ((N : ℚ) + k + 1) • pderiv (a, b) (hX N (k + 1)) := by
  classical
  ext m
  rw [← matExp_toMat m]
  set M : Fin N → Fin N → ℕ := fun i j => m (i, j)
  rw [coeff_sum, AddMonoidAlgebra.coeff_smul_apply]
  simp_rw [coeff_pderiv]
  simp_rw [← matExp_addE, coeff_hX, matExp_apply, hCond_addE_addE, smul_eq_mul]
  split_ifs with hc
  · have hrow : ∀ c, rowSum (addE (addE M a c) c b)
        = fun i => rowSum (addE M a b) i + if i = c then 1 else 0 := by
      intro c
      funext i
      rw [rowSum_addE, rowSum_addE, rowSum_addE]
    have hterm : ∀ c, hCoeff (rowSum (addE (addE M a c) c b)) (addE (addE M a c) c b)
        * ((addE M a c c b : ℚ) + 1) * ((M a c : ℚ) + 1)
        = ((rowSum (addE M a b) c : ℚ) + 1) * hCoeff (rowSum (addE M a b)) M := by
      intro c
      rw [hCoeff_addE, hCoeff_addE, hrow, hCoeff_bumpVec]
    simp_rw [hterm]
    rw [← sum_mul, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      hCoeff_addE]
    have hk : (∑ i, (rowSum (addE M a b) i : ℚ)) = k + 1 := by exact_mod_cast hc.2
    rw [hk]
    ring
  · simp

/-! ## All powers `∂^n` on rows -/

theorem prod_range_succ_shift (A : ℚ) (n : ℕ) :
    ∏ i ∈ range (n + 1), (A + i) = A * ∏ i ∈ range n, (A + 1 + i) := by
  rw [prod_range_succ', mul_comm]
  congr 1
  · simp
  · refine prod_congr rfl fun i _ => ?_
    push_cast
    ring

/-- **`(∂^{n+1})_{ab} h_{k+n+1}(X) = (N + k + 1) ⋯ (N + k + n) · ∂_{ab} h_{k+1}(X)`.** -/
theorem pathD_hX (n k : ℕ) (a b : Fin N) :
    pathD (n + 1) a b (hX N (k + n + 1))
      = (∏ i ∈ range n, ((N : ℚ) + k + 1 + i)) • pderiv (a, b) (hX N (k + 1)) := by
  induction n generalizing k a with
  | zero => simp [pathD_one]
  | succ n ih =>
    rw [pathD_succ, show k + (n + 1) + 1 = (k + 1) + n + 1 by omega]
    simp_rw [ih (k + 1), Derivation.map_smul]
    rw [← smul_sum, show k + 1 + 1 = k + 2 by omega, sqD_hX, smul_smul, prod_range_succ_shift,
      mul_comm]
    congr 2
    refine prod_congr rfl fun i _ => ?_
    push_cast
    ring

/-- **The Fock adjoint of `p_{n+1}(X)` on rows**:
`tr(∂^{n+1}) h_{k+n+1}(X) = (N + k)(N + k + 1) ⋯ (N + k + n) · h_k(X)`, the content-weighted
removal of the last `n + 1` boxes of the row. -/
theorem trDp_hX (n k : ℕ) :
    trDp (n + 1) (hX N (k + n + 1)) = (∏ i ∈ range (n + 1), ((N : ℚ) + k + i)) • hX N k := by
  rw [trDp]
  simp_rw [pathD_hX]
  rw [← smul_sum, ← trD_apply, trD_hX, smul_smul, prod_range_succ_shift, mul_comm]

/-- **`⟨p_ρ(X), h_k(X)⟩_Fock = N (N + 1) ⋯ (N + k − 1)`** for every composition `ρ` of `k` (a list
of positive parts summing to `k`): the twisted Hall pairing `χ^{(k)}(ρ) w_∞((k))`, with
`χ^{(k)} = 1`. -/
theorem fischer_prod_pX_hX (ρ : List ℕ) (hρ : ∀ j ∈ ρ, 0 < j) :
    fischer (ρ.map (pX N)).prod (hX N ρ.sum) = ∏ i ∈ range ρ.sum, ((N : ℚ) + i) := by
  induction ρ with
  | nil => simp [hX_zero, fischer_one_one]
  | cons j ρ ih =>
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by have := hρ j (by simp); omega⟩
    rw [List.map_cons, List.prod_cons, List.sum_cons, fischer_pX_mul,
      show n + 1 + ρ.sum = ρ.sum + n + 1 by omega, trDp_hX, smul_eq_C_mul, fischer_C_mul_right,
      ih fun j hj => hρ j (by simp [hj]), show ρ.sum + n + 1 = ρ.sum + (n + 1) by omega,
      prod_range_add (fun i : ℕ => ((N : ℚ) + i)), mul_comm]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    push_cast
    ring

end RMT.Fock
