import RMTlib.Fock.Rows

/-!
# The row and the column are Fock-orthogonal

The content-twisted Hall pairing (`RMTlib.Fock.ClassFunction`) predicts
`⟨s_λ(X), s_μ(X)⟩_Fock = δ_{λμ} ∏_{□ ∈ λ} (N + c(□))`. The diagonal is proved for the row
(`RMT.Fock.fischer_hX`) and the column (`RMT.Fock.fischer_eX`). This file proves the first
off-diagonal entry, between the two:

  `⟨h_k(X), e_k(X)⟩_Fock = C(N, k) · [k ≤ 1]`,

so `0` for `k ≥ 2`, where `(k) ≠ (1^k)` (`fischer_hX_eX`, `fischer_hX_eX_eq_zero`).

The proof is a count, as for the column. The monomials of `e_k(X)` are the permutation monomials
`∏_{i ∈ S} x_{π(i), i}`, with coefficient `sign π`. In `h_k(X)` the same monomial has coefficient
`1` (`coeff_hX_expo`): it is the term of `X` on `Sym^k` at the basis vector `∏_{i ∈ S} y_i`
indexed by the matrix of `π`, and `∏ α! / ∏ M! = 1` there. So the pairing is
`Σ_{|S| = k} Σ_{π ∈ Perm S} sign π`, and the inner sum is the determinant of the all-ones matrix.

## Main results

* `fischer_monomial_left`: `⟨c x^t, g⟩ = c · g_t · t!`.
* `coeff_hX_expo`: the permutation monomials have coefficient `1` in `h_k(X)`.
* `fischer_hX_eX`: `⟨h_k(X), e_k(X)⟩_Fock = C(N, k) · Σ_{π ∈ S_k} sign π`.
* `fischer_hX_eX_eq_zero`: `⟨h_k(X), e_k(X)⟩_Fock = 0` for `k ≥ 2`.
-/

open MvPolynomial Finset

namespace RMT.Fock

variable {σ : Type*} {N : ℕ}

theorem fischer_monomial_left (t : σ →₀ ℕ) (c : ℚ) (g : MvPolynomial σ ℚ) :
    fischer (monomial t c) g = c * g.coeff t * ((∏ k ∈ t.support, (t k).factorial : ℕ) : ℚ) := by
  classical
  rw [fischer_eq_sum_of_subset _ _ {t} support_monomial_subset, sum_singleton, coeff_monomial,
    if_pos rfl]

/-- `e_k(X)` as a sum of permutation monomials, over pairs (subset `S`, permutation of `S`). -/
theorem eX_eq_sum (k : ℕ) :
    eX N k = ∑ p ∈ (powersetCard k (univ : Finset (Fin N))).sigma
      (fun S => (univ : Finset (Equiv.Perm S))),
      monomial (expo p.1 p.2) (((Equiv.Perm.sign p.2 : ℤ) : ℚ)) := by
  rw [eX, Finset.sum_sigma]
  exact sum_congr rfl fun S _ => minor_eq S

/-- The indicator of `S`, the weight of the basis vector `∏_{i ∈ S} y_i` of `Sym^k`. -/
def indic (S : Finset (Fin N)) : Fin N → ℕ := fun i => if i ∈ S then 1 else 0

/-- The matrix of the permutation `π` of `S`: `M i j = 1` iff `j ∈ S` and `π j = i`. -/
noncomputable def permMat (S : Finset (Fin N)) (π : Equiv.Perm S) : Fin N → Fin N → ℕ :=
  fun i j => expo S π (i, j)

theorem matExp_permMat (S : Finset (Fin N)) (π : Equiv.Perm S) :
    matExp (permMat S π) = expo S π := by
  ext ⟨i, j⟩
  rfl

theorem permMat_le_one (S : Finset (Fin N)) (π : Equiv.Perm S) (i j : Fin N) :
    permMat S π i j ≤ 1 := expo_le_one S π (i, j)

/-- Column sums of the permutation matrix. -/
theorem sum_permMat_col (S : Finset (Fin N)) (π : Equiv.Perm S) (j : Fin N) :
    ∑ i, permMat S π i j = indic S j := by
  classical
  unfold permMat indic
  simp_rw [expo_apply]
  by_cases hj : j ∈ S
  · simp only [dif_pos hj, if_pos hj]
    rw [Fintype.sum_eq_single (π ⟨j, hj⟩).1 fun i hi => if_neg (Ne.symm hi), if_pos rfl]
  · simp [dif_neg hj, if_neg hj]

/-- Row sums of the permutation matrix: `π` is a bijection of `S`. -/
theorem sum_permMat_row (S : Finset (Fin N)) (π : Equiv.Perm S) (i : Fin N) :
    ∑ j, permMat S π i j = indic S i := by
  classical
  unfold permMat indic
  simp_rw [expo_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi, Fintype.sum_eq_single (π.symm ⟨i, hi⟩).1]
    · rw [dif_pos (π.symm ⟨i, hi⟩).2]
      simp
    · intro j hj
      split_ifs with h1 h2
      · exfalso
        apply hj
        have : π ⟨j, h1⟩ = ⟨i, hi⟩ := Subtype.ext h2
        rw [← this, Equiv.symm_apply_apply]
      · rfl
      · rfl
  · rw [if_neg hi]
    refine sum_eq_zero fun j _ => ?_
    split_ifs with h1 h2
    · exact absurd (h2 ▸ (π ⟨j, h1⟩).2) hi
    · rfl
    · rfl

theorem sum_indic (S : Finset (Fin N)) : ∑ i, indic S i = #S := by
  classical
  simp [indic]

theorem hCoeff_permMat (S : Finset (Fin N)) (π : Equiv.Perm S) :
    hCoeff (indic S) (permMat S π) = 1 := by
  have h1 : ∀ i, (indic S i).factorial = 1 := fun i => by
    unfold indic; split_ifs <;> rfl
  have h2 : ∀ i j, (permMat S π i j).factorial = 1 := fun i j => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (permMat_le_one S π i j) with h | h <;> rw [h] <;> rfl
  simp [hCoeff, h1, h2]

/-- **The permutation monomials have coefficient `1` in `h_k(X)`.** -/
theorem coeff_hX_expo {k : ℕ} {S : Finset (Fin N)} (hS : #S = k) (π : Equiv.Perm S) :
    (hX N k).coeff (expo S π) = 1 := by
  classical
  have hsum : hX N k = ∑ p ∈ (Nat.antidiagonalTuple N k).sigma (fun α => margins N α α),
      monomial (matExp p.2) (hCoeff p.1 p.2) := by
    rw [hX, sum_sigma]
  have hmem : (⟨indic S, permMat S π⟩ : Σ _ : Fin N → ℕ, Fin N → Fin N → ℕ) ∈
      (Nat.antidiagonalTuple N k).sigma (fun α => margins N α α) := by
    refine mem_sigma.mpr ⟨Nat.mem_antidiagonalTuple.mpr (by rw [sum_indic, hS]), ?_⟩
    exact mem_margins.mpr ⟨sum_permMat_row S π, sum_permMat_col S π⟩
  rw [hsum, coeff_sum, sum_eq_single_of_mem _ hmem]
  · rw [coeff_monomial, matExp_permMat, if_pos rfl, hCoeff_permMat]
  · rintro ⟨α, M⟩ hp hne
    rw [coeff_monomial, if_neg]
    intro h
    apply hne
    rw [← matExp_permMat] at h
    obtain rfl : M = permMat S π := matExp_injective h
    have hα := (mem_margins.mp (mem_sigma.mp hp).2).1
    obtain rfl : α = indic S := funext fun i => (hα i).symm.trans (sum_permMat_row S π i)
    rfl

/-- The sum of the signs of the permutations of a finite type is the determinant of the all-ones
matrix. -/
theorem sum_sign_eq_det (S : Type*) [Fintype S] [DecidableEq S] :
    (∑ π : Equiv.Perm S, ((Equiv.Perm.sign π : ℤ) : ℚ))
      = (Matrix.of fun _ _ : S => (1 : ℚ)).det := by
  rw [Matrix.det_apply]
  refine sum_congr rfl fun π _ => ?_
  simp [Units.smul_def]

/-- **The sum of the signs vanishes on at least two letters.** -/
theorem sum_sign_eq_zero {S : Type*} [Fintype S] [DecidableEq S] (h : 2 ≤ Fintype.card S) :
    (∑ π : Equiv.Perm S, ((Equiv.Perm.sign π : ℤ) : ℚ)) = 0 := by
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card h
  rw [sum_sign_eq_det]
  exact Matrix.det_zero_of_row_eq hxy rfl

/-- **The pairing of the row and the column**: `⟨h_k(X), e_k(X)⟩_Fock = C(N, k) Σ_{π ∈ S_k} sign π`. -/
theorem fischer_hX_eX (k : ℕ) :
    fischer (hX N k) (eX N k)
      = (N.choose k : ℚ) * ∑ π : Equiv.Perm (Fin k), ((Equiv.Perm.sign π : ℤ) : ℚ) := by
  classical
  rw [eX_eq_sum, fischer_sum_right, sum_sigma]
  have hS : ∀ S ∈ powersetCard k (univ : Finset (Fin N)),
      ∑ π ∈ (univ : Finset (Equiv.Perm S)),
        fischer (hX N k) (monomial (expo S π) (((Equiv.Perm.sign π : ℤ) : ℚ)))
      = ∑ π : Equiv.Perm (Fin k), ((Equiv.Perm.sign π : ℤ) : ℚ) := by
    intro S hS
    have hk := (mem_powersetCard.mp hS).2
    have hterm : ∀ π : Equiv.Perm S,
        fischer (hX N k) (monomial (expo S π) (((Equiv.Perm.sign π : ℤ) : ℚ)))
          = ((Equiv.Perm.sign π : ℤ) : ℚ) := by
      intro π
      rw [fischer_comm, fischer_monomial_left, coeff_hX_expo hk, prod_factorial_expo]
      simp
    rw [sum_congr rfl fun π _ => hterm π]
    let e : S ≃ Fin k := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hk])
    exact Fintype.sum_equiv (Equiv.permCongr e) _ _ fun π => by
      rw [Equiv.Perm.sign_permCongr]
  rw [sum_congr rfl hS, sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The row and the column are Fock-orthogonal**: `⟨h_k(X), e_k(X)⟩_Fock = 0` for `k ≥ 2`, the
off-diagonal case `(k) ≠ (1^k)` of the content-twisted Hall pairing. -/
theorem fischer_hX_eX_eq_zero {k : ℕ} (hk : 2 ≤ k) : fischer (hX N k) (eX N k) = 0 := by
  rw [fischer_hX_eX, sum_sign_eq_zero (by simpa using hk), mul_zero]

end RMT.Fock
