import RMTlib.Fock.Orthogonality
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The Fock adjoint of `tr X` removes one box, with weight `N + c`

For an `N × N` matrix of variables `X`, the Fock (Fischer) adjoint of multiplication by
`tr X = p₁(X)` is the trace Laplacian `Δ = Σ_a ∂/∂x_{aa}` (`fischer_trX_mul`, from the adjointness
of `x_v` and `∂/∂x_v`). On Schur functions of `X` it acts by removing one box, weighted by
`N + c` where `c` is the content of the box removed:

  `Δ s_λ(X) = Σ_i (N + λ_i − 1 − i) · s_{λ − e_i}(X)`   (`trD_sX`).

Here `s_λ(X)` is defined for every integer vector `λ` by the Jacobi–Trudi determinant
`det (h_{λ_i − i + j}(X))` (`sX`), with `h_k(X)` the trace of `X` on `Sym^k` (`RMT.Fock.hX`) and
`h_k = 0` for `k < 0`. The term `i` is the removal of the last box `(i, λ_i − 1)` of row `i`, of
content `λ_i − 1 − i`. When `λ − e_i` is not a partition (`λ_i = λ_{i+1}`), the Jacobi–Trudi
determinant has two equal rows and the term vanishes.

So the archimedean weight `w_∞(λ) = ∏_{□ ∈ λ} (N + c(□))` is the product of the factors the Fock
adjoint of `p₁` picks up as it strips `λ` box by box. The content-twisted Hall pairing
`⟨s_λ, s_μ⟩ = δ_{λμ} w_∞(λ)` has the same adjoint pair: there,
`⟨p₁ s_ν, s_μ⟩ = [ν ⋖ μ] w_∞(μ) = [ν ⋖ μ] (N + c(μ/ν)) w_∞(ν)`. That `p₁` and `Δ` are adjoint
for both pairings is what is proved; it does not by itself identify the two pairings (see
`bridge/links/fock-norm.md`).

## The steps

* `trD_hX`: `Δ h_{k+1}(X) = (N + k) h_k(X)`, the row case, by comparing coefficients: the
  coefficient of `x^M` in `h_k(X)` is `∏ α! / ∏ M!` when both margins of `M` are `α`
  (`coeff_hX`).
* `derivation_det`: a derivation applied to a determinant is the sum over rows of the determinants
  with that row differentiated.
* The row `i` of the differentiated Jacobi–Trudi matrix is `(N + λ_i − 1 − i)` times the row of
  `λ − e_i`, plus the row `j ↦ j · h_{λ_i − i + j − 1}`. The second rows are `A C` for the
  strictly upper triangular `C` with `C_{j−1, j} = j`, and contribute `tr C · det A = 0`
  (`sum_det_updateRow_mul`, via the adjugate).

## Main results

* `fischer_trX_mul`: `⟨tr X · f, g⟩_Fock = ⟨f, Δ g⟩_Fock`.
* `hX_zero`: `h_0(X) = 1`.
* `trD_hX`: `Δ h_{k+1}(X) = (N + k) h_k(X)`.
* `trD_sX`: `Δ s_λ(X) = Σ_i (N + λ_i − 1 − i) s_{λ − e_i}(X)` for every `λ ∈ ℤ^ℓ`.
* `fischer_trX_mul_sX`: `⟨tr X · f, s_λ(X)⟩_Fock = Σ_i (N + λ_i − 1 − i) ⟨f, s_{λ − e_i}(X)⟩_Fock`.
* `fischer_trX_pow_sX`: `⟨(tr X)^m, s_λ(X)⟩_Fock = f^λ ∏_{(i, c) ∈ λ} (N + c − i)` for every
  partition `λ ⊢ m`: each removal chain picks up the same product, and there are `f^λ` chains.
* `eq_zero_of_fischer_self`, `hX_one`: the pairing is definite; `h_1(X) = tr X`.
* `fischer_sX_two_one`: `‖s_{(2,1)}(X)‖²_Fock = (N − 1) N (N + 1)`, the first shape that is neither
  a row nor a column, from the adjoint pair `(tr X, Δ)` and the norms of the rows.
-/

open MvPolynomial Finset

namespace RMT.Fock

variable {N : ℕ}

/-! ## The trace Laplacian -/

variable (N) in
/-- The trace Laplacian `Δ = Σ_a ∂/∂x_{aa}`, the Fock adjoint of multiplication by `tr X`. -/
noncomputable def trD : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ) :=
  ∑ a, pderiv (a, a)

theorem trD_apply (f : MvPolynomial (Fin N × Fin N) ℚ) : trD N f = ∑ a, pderiv (a, a) f := by
  rw [trD, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

/-- **The Fock adjoint of `tr X` is the trace Laplacian.** -/
theorem fischer_trX_mul (f g : MvPolynomial (Fin N × Fin N) ℚ) :
    fischer (trX N * f) g = fischer f (trD N g) := by
  rw [trX, sum_mul, fischer_sum_left, trD_apply, fischer_sum_right]
  exact sum_congr rfl fun a _ => fischer_X_mul_left _ _ _

/-! ## The coefficients of `h_k(X)` -/

/-- Row sums of a matrix of naturals. -/
def rowSum (M : Fin N → Fin N → ℕ) : Fin N → ℕ := fun i => ∑ j, M i j

/-- The condition for `x^M` to occur in `h_k(X)`: row sums equal column sums, total `k`. -/
def HCond (k : ℕ) (M : Fin N → Fin N → ℕ) : Prop :=
  (∀ j, ∑ i, M i j = rowSum M j) ∧ ∑ i, rowSum M i = k

theorem hCond_iff (k : ℕ) (M : Fin N → Fin N → ℕ) :
    HCond k M ↔ M ∈ margins N (rowSum M) (rowSum M) ∧ ∑ i, rowSum M i = k := by
  rw [mem_margins, HCond]
  exact ⟨fun h => ⟨⟨fun _ => rfl, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

open Classical in
/-- **The coefficient of `x^M` in `h_k(X)`** is `∏ α! / ∏ M!` when both margins of `M` are `α`
and `|α| = k`, and `0` otherwise. -/
theorem coeff_hX (k : ℕ) (M : Fin N → Fin N → ℕ) :
    (hX N k).coeff (matExp M) = if HCond k M then hCoeff (rowSum M) M else 0 := by
  have hsum : hX N k = ∑ p ∈ (Nat.antidiagonalTuple N k).sigma (fun α => margins N α α),
      monomial (matExp p.2) (hCoeff p.1 p.2) := by
    rw [hX, sum_sigma]
  rw [hsum, coeff_sum]
  simp_rw [coeff_monomial]
  split_ifs with hc <;> rw [hCond_iff] at hc
  · have hmem : (⟨rowSum M, M⟩ : Σ _ : Fin N → ℕ, Fin N → Fin N → ℕ) ∈
        (Nat.antidiagonalTuple N k).sigma (fun α => margins N α α) :=
      mem_sigma.mpr ⟨Nat.mem_antidiagonalTuple.mpr hc.2, hc.1⟩
    rw [sum_eq_single_of_mem _ hmem, ite_eq_left rfl]
    rintro ⟨α, M'⟩ hp hne
    rw [ite_eq_right]
    intro h
    apply hne
    obtain rfl : M = M' := (matExp_injective h).symm
    have hα := (mem_margins.mp (mem_sigma.mp hp).2).1
    obtain rfl : α = rowSum M := funext fun i => (hα i).symm
    rfl
  · refine sum_eq_zero fun p hp => ite_eq_right fun h => hc ?_
    obtain ⟨α, M'⟩ := p
    obtain rfl : M = M' := (matExp_injective h).symm
    have hp' := mem_sigma.mp hp
    have hα := (mem_margins.mp hp'.2).1
    obtain rfl : α = rowSum M := funext fun i => (hα i).symm
    exact ⟨hp'.2, Nat.mem_antidiagonalTuple.mp hp'.1⟩

theorem matExp_toMat (m : Fin N × Fin N →₀ ℕ) : matExp (fun i j => m (i, j)) = m := by
  ext ⟨i, j⟩
  rfl

/-- `h_0(X) = 1`. -/
theorem hX_zero : hX N 0 = 1 := by
  classical
  ext m
  rw [← matExp_toMat m, coeff_hX, coeff_one]
  set M : Fin N → Fin N → ℕ := fun i j => m (i, j)
  by_cases hM : M = 0
  · have hm : matExp M = 0 := by rw [hM]; ext; rfl
    have hc : HCond 0 M := by
      refine ⟨fun j => ?_, ?_⟩ <;> simp [rowSum, hM]
    rw [ite_eq_left hc, hm, ite_eq_left rfl]
    simp [hCoeff, rowSum, hM]
  · have hm : matExp M ≠ 0 := by
      intro h
      apply hM
      funext i j
      exact congrArg (fun f => f (i, j)) h
    rw [ite_eq_right (Ne.symm hm), ite_eq_right]
    rintro ⟨-, h0⟩
    apply hM
    funext i j
    have h1 : ∑ i, ∑ j, M i j = 0 := h0
    rw [sum_eq_zero_iff] at h1
    exact (sum_eq_zero_iff.mp (h1 i (mem_univ _))) j (mem_univ _)

/-- `M` with one more unit at the diagonal entry `(a, a)`. -/
def bump (M : Fin N → Fin N → ℕ) (a : Fin N) : Fin N → Fin N → ℕ :=
  fun i j => M i j + if i = a ∧ j = a then 1 else 0

theorem matExp_bump (M : Fin N → Fin N → ℕ) (a : Fin N) :
    matExp (bump M a) = matExp M + Finsupp.single (a, a) 1 := by
  ext ⟨i, j⟩
  simp only [matExp_apply, bump, Finsupp.add_apply, Finsupp.single_apply, Prod.ext_iff]
  by_cases h : i = a ∧ j = a
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [ite_eq_right h, ite_eq_right (by tauto)]

theorem sum_ite_eq_single (a : Fin N) (j : Fin N) :
    (∑ i : Fin N, if i = a ∧ j = a then 1 else 0) = if j = a then 1 else 0 := by
  by_cases hj : j = a
  · simp [hj]
  · simp [hj]

theorem rowSum_bump (M : Fin N → Fin N → ℕ) (a i : Fin N) :
    rowSum (bump M a) i = rowSum M i + if i = a then 1 else 0 := by
  unfold rowSum bump
  rw [sum_add_distrib]
  congr 1
  by_cases hi : i = a
  · subst hi; simp
  · simp [hi]

theorem colSum_bump (M : Fin N → Fin N → ℕ) (a j : Fin N) :
    ∑ i, bump M a i j = ∑ i, M i j + if j = a then 1 else 0 := by
  unfold bump
  rw [sum_add_distrib, sum_ite_eq_single]

theorem hCond_bump (k : ℕ) (M : Fin N → Fin N → ℕ) (a : Fin N) :
    HCond (k + 1) (bump M a) ↔ HCond k M := by
  unfold HCond
  simp only [rowSum_bump, colSum_bump, sum_add_distrib, sum_ite_eq', mem_univ, ite_true,
    add_left_inj]

theorem prod_factorial_bump_vec (α : Fin N → ℕ) (a : Fin N) :
    (∏ i, (α i + if i = a then 1 else 0).factorial) = (α a + 1) * ∏ i, (α i).factorial := by
  rw [← mul_prod_erase univ _ (mem_univ a), ← mul_prod_erase univ (fun i => (α i).factorial)
    (mem_univ a), ite_eq_left rfl, Nat.factorial_succ, mul_assoc]
  congr 2
  refine prod_congr rfl fun i hi => ?_
  rw [ite_eq_right (ne_of_mem_erase hi), add_zero]

theorem prod_factorial_bump (M : Fin N → Fin N → ℕ) (a : Fin N) :
    (∏ i, ∏ j, (bump M a i j).factorial) = (M a a + 1) * ∏ i, ∏ j, (M i j).factorial := by
  have h : ∀ i, (∏ j, (bump M a i j).factorial)
      = if i = a then (M a a + 1) * ∏ j, (M a j).factorial else ∏ j, (M i j).factorial := by
    intro i
    by_cases hi : i = a
    · subst hi
      rw [ite_eq_left rfl, ← prod_factorial_bump_vec]
      refine prod_congr rfl fun j _ => ?_
      by_cases hj : j = i <;> simp [bump, hj]
    · rw [ite_eq_right hi]
      refine prod_congr rfl fun j _ => ?_
      simp [bump, hi]
  simp_rw [h]
  rw [← mul_prod_erase univ _ (mem_univ a), ← mul_prod_erase univ
    (fun i => ∏ j, (M i j).factorial) (mem_univ a), ite_eq_left rfl, mul_assoc]
  congr 2
  exact prod_congr rfl fun i hi => ite_eq_right (ne_of_mem_erase hi)

theorem hCoeff_bump (M : Fin N → Fin N → ℕ) (a : Fin N) :
    hCoeff (rowSum (bump M a)) (bump M a) * ((M a a : ℚ) + 1)
      = ((rowSum M a : ℚ) + 1) * hCoeff (rowSum M) M := by
  unfold hCoeff
  rw [show rowSum (bump M a) = fun i => rowSum M i + if i = a then 1 else 0 from
    funext (rowSum_bump M a), prod_factorial_bump_vec, prod_factorial_bump]
  have h1 : ((∏ i, ∏ j, (M i j).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have h2 : (M a a : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- **`Δ h_{k+1}(X) = (N + k) h_k(X)`**: removing the box of content `k` from the row. -/
theorem trD_hX (k : ℕ) : trD N (hX N (k + 1)) = ((N : ℚ) + k) • hX N k := by
  classical
  ext m
  rw [← matExp_toMat m]
  set M : Fin N → Fin N → ℕ := fun i j => m (i, j)
  rw [trD_apply, coeff_sum, coeff_smul]
  simp_rw [coeff_pderiv, ← matExp_bump, coeff_hX, matExp_apply]
  simp_rw [hCond_bump]
  split_ifs with hc
  · simp_rw [hCoeff_bump]
    rw [← sum_mul, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    have hk : (∑ a, (rowSum M a : ℚ)) = k := by exact_mod_cast hc.2
    rw [hk]
    ring
  · simp

/-! ## A derivation of a determinant -/

section Det

variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem derivation_prod {ι : Type*} [DecidableEq ι] (D : Derivation ℚ A A) (s : Finset ι)
    (f : ι → A) : D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, D.leibniz, ih, sum_insert ha, erase_insert ha, smul_eq_mul, smul_eq_mul,
      mul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    rw [erase_insert_of_ne (Ne.symm hia), prod_insert (fun h => ha (mem_of_mem_erase h)), mul_assoc]

/-- **A derivation of a determinant**: the sum over rows of the determinants with that row
differentiated. -/
theorem derivation_det {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation ℚ A A)
    (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j => D (M i j)).det := by
  simp_rw [Matrix.det_apply, map_sum, Units.smul_def]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rw [map_zsmul, derivation_prod, smul_sum]
  refine Fintype.sum_equiv σ _ _ fun i => ?_
  congr 1
  rw [← mul_prod_erase univ _ (mem_univ i), Matrix.updateRow_self, mul_comm]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  rw [Matrix.updateRow_ne fun h => ne_of_mem_erase hj (σ.injective h)]

omit [Algebra ℚ A] in
/-- **Determinant with a row replaced, by the adjugate**: `det (A with row i := v) = Σ_j v_j adj(A)_{ji}`. -/
theorem det_updateRow_eq_sum_adjugate {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n A)
    (i : n) (v : n → A) : (M.updateRow i v).det = ∑ j, v j * M.adjugate j i := by
  rw [Matrix.det_eq_sum_mul_adjugate_row _ i]
  refine sum_congr rfl fun j _ => ?_
  rw [Matrix.updateRow_self, Matrix.adjugate_apply, Matrix.adjugate_apply, Matrix.updateRow_idem]

omit [Algebra ℚ A] in
/-- **Rows replaced by the rows of `A C`** contribute `tr C · det A`. -/
theorem sum_det_updateRow_mul {n : Type*} [Fintype n] [DecidableEq n] (M Cm : Matrix n n A) :
    ∑ i, (M.updateRow i ((M * Cm) i)).det = Cm.trace * M.det := by
  simp_rw [det_updateRow_eq_sum_adjugate, Matrix.mul_apply, sum_mul]
  rw [sum_comm]
  have h : ∀ j : n, ∑ i, ∑ l, M i l * Cm l j * M.adjugate j i = Cm j j * M.det := by
    intro j
    rw [sum_comm]
    have h2 : ∀ l, ∑ i, M i l * Cm l j * M.adjugate j i = Cm l j * (M.adjugate * M) j l := by
      intro l
      rw [Matrix.mul_apply, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    rw [sum_congr rfl fun l _ => h2 l]
    simp only [Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    rw [sum_ite_eq, ite_eq_left (mem_univ _)]
  simp_rw [h]
  rw [← sum_mul, Matrix.trace]
  rfl

end Det

/-! ## Schur functions of `X` by Jacobi–Trudi -/

variable (N) in
/-- `h_z(X)` for an integer `z`: `0` for `z < 0`. -/
noncomputable def hZ (z : ℤ) : MvPolynomial (Fin N × Fin N) ℚ := if 0 ≤ z then hX N z.toNat else 0

/-- **`Δ h_z(X) = (N + z − 1) h_{z−1}(X)`** for every integer `z`. -/
theorem trD_hZ (z : ℤ) : trD N (hZ N z) = ((N : ℚ) + z - 1) • hZ N (z - 1) := by
  unfold hZ
  by_cases h0 : 0 ≤ z - 1
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = k + 1 := ⟨(z - 1).toNat, by omega⟩
    subst hk
    rw [ite_eq_left (by omega), ite_eq_left h0, show ((k : ℤ) + 1).toNat = k + 1 by omega,
      show ((k : ℤ) + 1 - 1).toNat = k by omega, trD_hX]
    push_cast
    ring_nf
  · rw [ite_eq_right h0, smul_zero]
    split_ifs with h1
    · rw [show z.toNat = 0 by omega, hX_zero, Derivation.map_one_eq_zero]
    · exact map_zero _

variable (N) in
/-- **The Schur function of `X` by Jacobi–Trudi**, for every integer vector `λ`:
`s_λ(X) = det (h_{λ_i − i + j}(X))`. -/
noncomputable def sX {l : ℕ} (lam : Fin l → ℤ) : MvPolynomial (Fin N × Fin N) ℚ :=
  (Matrix.of fun i j : Fin l => hZ N (lam i - i + j)).det

theorem sX_row (k : ℕ) : sX N (fun _ : Fin 1 => (k : ℤ)) = hX N k := by
  simp [sX, hZ]

/-- The row `j ↦ j · h_{λ_i − i + j − 1}` is row `i` of `A C`, `C_{j−1, j} = j`. -/
theorem shift_row_eq {l : ℕ} (lam : Fin l → ℤ) (i j : Fin l) :
    ((j : ℕ) : MvPolynomial (Fin N × Fin N) ℚ) * hZ N (lam i - i + j - 1)
      = ((Matrix.of fun i j : Fin l => hZ N (lam i - i + j) :
            Matrix (Fin l) (Fin l) (MvPolynomial (Fin N × Fin N) ℚ)) *
          (Matrix.of fun a b : Fin l => if (a : ℕ) + 1 = b then ((b : ℕ) : MvPolynomial _ ℚ) else 0 :
            Matrix (Fin l) (Fin l) (MvPolynomial (Fin N × Fin N) ℚ))) i j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, mul_ite, mul_zero]
  by_cases hj : (j : ℕ) = 0
  · rw [hj, Nat.cast_zero, zero_mul]
    refine (sum_eq_zero fun a _ => ite_eq_right (by omega)).symm
  · have hlt : (j : ℕ) - 1 < l := by omega
    rw [sum_eq_single ⟨(j : ℕ) - 1, hlt⟩]
    · rw [ite_eq_left (by simp; omega), mul_comm]
      congr 2
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj)]
      ring
    · intro a _ ha
      rw [ite_eq_right]
      intro h
      apply ha
      ext
      simp only
      omega
    · simp

/-- **The Fock adjoint of `tr X` removes one box, with weight `N + c`**:
`Δ s_λ(X) = Σ_i (N + λ_i − 1 − i) · s_{λ − e_i}(X)`, for every integer vector `λ`. The term `i`
removes the last box of row `i`, of content `λ_i − 1 − i`. -/
theorem trD_sX {l : ℕ} (lam : Fin l → ℤ) :
    trD N (sX N lam) = ∑ i : Fin l, ((N : ℚ) + lam i - 1 - i) •
      sX N (Function.update lam i (lam i - 1)) := by
  classical
  set A : Matrix (Fin l) (Fin l) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun i j : Fin l => hZ N (lam i - i + j)
  set Cm : Matrix (Fin l) (Fin l) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun a b : Fin l => if (a : ℕ) + 1 = b then ((b : ℕ) : MvPolynomial _ ℚ) else 0
  have hrow : ∀ i : Fin l, (fun j => trD N (A i j))
      = (C ((N : ℚ) + lam i - 1 - i) : MvPolynomial (Fin N × Fin N) ℚ) •
          (fun j : Fin l => hZ N (lam i - 1 - i + j)) + (A * Cm) i := by
    intro i
    funext j
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← shift_row_eq lam i j]
    simp only [A, Matrix.of_apply, trD_hZ]
    rw [show lam i - 1 - (i : ℤ) + j = lam i - i + j - 1 by ring, smul_eq_C_mul, ← add_mul]
    congr 1
    rw [← map_natCast (C : ℚ →+* MvPolynomial (Fin N × Fin N) ℚ), ← map_add]
    congr 1
    push_cast
    ring
  have hupd : ∀ i : Fin l, A.updateRow i (fun j : Fin l => hZ N (lam i - 1 - i + j))
      = Matrix.of fun i' j : Fin l => hZ N (Function.update lam i (lam i - 1) i' - i' + j) := by
    intro i
    ext i' j
    by_cases h : i' = i
    · subst h
      simp
    · simp [A, Matrix.updateRow_ne h, Function.update_of_ne h]
  rw [show sX N lam = A.det from rfl, derivation_det]
  simp_rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, hupd]
  rw [sum_add_distrib, sum_det_updateRow_mul]
  have htr : Cm.trace = 0 := by
    refine sum_eq_zero fun j _ => ?_
    simp [Cm]
  rw [htr, zero_mul, add_zero]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul]
  rfl

/-- **`⟨tr X · f, s_λ(X)⟩_Fock = Σ_i (N + λ_i − 1 − i) ⟨f, s_{λ − e_i}(X)⟩_Fock`.** -/
theorem fischer_trX_mul_sX {l : ℕ} (f : MvPolynomial (Fin N × Fin N) ℚ) (lam : Fin l → ℤ) :
    fischer (trX N * f) (sX N lam) = ∑ i : Fin l, ((N : ℚ) + lam i - 1 - i) *
      fischer f (sX N (Function.update lam i (lam i - 1))) := by
  rw [fischer_trX_mul, trD_sX, fischer_sum_right]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, fischer_C_mul_right]

/-! ## The pairing with `(tr X)^m` -/

theorem fischer_zero_right {σ : Type*} (f : MvPolynomial σ ℚ) : fischer f 0 = 0 := by
  simp [fischer]

/-- `s_0(X) = 1`: the Jacobi–Trudi matrix of the empty shape is unitriangular. -/
theorem sX_zero (l : ℕ) : sX N (fun _ : Fin l => (0 : ℤ)) = 1 := by
  rw [sX, Matrix.det_of_isUpperTriangular]
  · refine prod_eq_one fun i _ => ?_
    simp [hZ, hX_zero]
  · intro i j hij
    have : (j : ℕ) < i := hij
    simp only [Matrix.of_apply, hZ]
    rw [ite_eq_right (by omega)]

/-- **Removing a box that is not a corner gives `0`**: the Jacobi–Trudi determinant of `λ − e_i`
has two equal rows, or a zero last row. -/
theorem sX_removeBox_eq_zero {l : ℕ} {ν : Fin l → ℕ} (hν : Antitone ν) {i : Fin l}
    (hi : IsCorner ν i = false) :
    sX N (Function.update (fun k => (ν k : ℤ)) i ((ν i : ℤ) - 1)) = 0 := by
  classical
  simp only [IsCorner, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hi
  by_cases h : (i : ℕ) + 1 < l
  · set i' : Fin l := ⟨(i : ℕ) + 1, h⟩
    have hii' : i ≤ i' := by simp [Fin.le_def, i']
    have hle := hν hii'
    have heq : ν i' = ν i := by
      rcases hi with h0 | h1
      · omega
      · rw [dite_eq_left h] at h1
        have : ¬ ν i' < ν i := by simpa using h1
        omega
    have hne : i ≠ i' := by simp [Fin.ext_iff, i']
    refine Matrix.det_zero_of_row_eq hne (funext fun j => ?_)
    simp only [Matrix.of_apply, Function.update_self, Function.update_of_ne (Ne.symm hne), heq]
    congr 1
    simp [i']
    ring
  · have h0 : ν i = 0 := by
      rcases hi with h0 | h1
      · omega
      · rw [dite_eq_right h] at h1; simp at h1
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    simp only [Matrix.of_apply, Function.update_self, h0, hZ]
    rw [ite_eq_right (by have := j.isLt; omega)]

variable (N) in
/-- The archimedean weight `∏_{(i, c)} (N + c − i)` of `ν`, rows of any length `l`. -/
def wQ {l : ℕ} (ν : Fin l → ℕ) : ℚ := ∏ i : Fin l, ∏ c ∈ range (ν i), ((N : ℚ) + c - i)

theorem wQ_removeBox {l : ℕ} {ν : Fin l → ℕ} {k : Fin l} (hk : 0 < ν k) :
    wQ N ν = ((N : ℚ) + (ν k - 1 : ℕ) - k) * wQ N (removeBox ν k) := by
  unfold wQ
  rw [← mul_prod_erase univ _ (mem_univ k), ← mul_prod_erase univ
    (fun i => ∏ c ∈ range (removeBox ν k i), ((N : ℚ) + c - i)) (mem_univ k), ← mul_assoc]
  congr 1
  · simp only [removeBox, Function.update_self]
    rw [show ν k = ν k - 1 + 1 by omega, prod_range_succ, Nat.add_sub_cancel, mul_comm]
  · refine prod_congr rfl fun i hi => ?_
    simp [removeBox, Function.update_of_ne (ne_of_mem_erase hi)]

/-- **The Fock pairing of `(tr X)^m` with `s_λ(X)` is `f^λ ∏_{(i, c) ∈ λ} (N + c − i)`**, for every
partition `λ ⊢ m` (with any number `l` of rows): the content-twisted Hall pairing against `p₁^m`,
for every shape. By `trD_sX`, each removal chain of `λ` contributes the product of the `N + c` of
the boxes it removes, which is the same for every chain, and there are `f^λ` chains. -/
theorem fischer_trX_pow_sX {l : ℕ} (m : ℕ) :
    ∀ ν : Fin l → ℕ, Antitone ν → ∑ i, ν i = m →
      fischer (trX N ^ m) (sX N fun i => (ν i : ℤ)) = (fSYT m ν : ℚ) * wQ N ν := by
  induction m with
  | zero =>
    intro ν _ hs
    have h0 : ν = 0 := funext fun i => by
      have := single_le_sum (fun j _ => Nat.zero_le (ν j)) (mem_univ i); simp at this ⊢; omega
    subst h0
    simp only [pow_zero, Pi.zero_apply, Nat.cast_zero]
    rw [sX_zero, fischer_one_one, fSYT, ite_eq_left (by simp)]
    simp [wQ]
  | succ m ih =>
    intro ν hν hs
    classical
    rw [pow_succ', fischer_trX_mul_sX, fSYT, ite_eq_right (by omega), Nat.cast_sum, sum_mul, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    split_ifs with hc
    · obtain ⟨hanti, hpos⟩ := removeBox_antitone hν hc
      have hupd : Function.update (fun k => (ν k : ℤ)) i ((ν i : ℤ) - 1)
          = fun k => (removeBox ν i k : ℤ) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [removeBox]; omega
        · simp [removeBox, Function.update_of_ne hk]
      have hsum : ∑ k, removeBox ν i k = m := by have := sum_removeBox hpos; omega
      rw [hupd, ih _ hanti hsum, wQ_removeBox hpos]
      push_cast [Nat.cast_sub hpos]
      ring
    · rw [sX_removeBox_eq_zero hν (by simpa using hc), fischer_zero_right, mul_zero]

/-! ## Beyond rows and columns: the shape `(2, 1)` -/

theorem fischer_C_mul_left {σ : Type*} (f g : MvPolynomial σ ℚ) (a : ℚ) :
    fischer (C a * f) g = a * fischer f g := by
  rw [fischer_comm, fischer_C_mul_right, fischer_comm]

theorem fischer_sub_left {σ : Type*} (f₁ f₂ g : MvPolynomial σ ℚ) :
    fischer (f₁ - f₂) g = fischer f₁ g - fischer f₂ g := by
  rw [sub_eq_add_neg, neg_eq_neg_one_mul, show (-1 : MvPolynomial σ ℚ) = C (-1) by simp,
    fischer_add_left, fischer_C_mul_left]
  ring

theorem fischer_sub_right {σ : Type*} (f g₁ g₂ : MvPolynomial σ ℚ) :
    fischer f (g₁ - g₂) = fischer f g₁ - fischer f g₂ := by
  rw [fischer_comm, fischer_sub_left, fischer_comm g₁, fischer_comm g₂]

/-- **The Fock pairing is definite**: `⟨f, f⟩_Fock = 0` only for `f = 0`. -/
theorem eq_zero_of_fischer_self {σ : Type*} {f : MvPolynomial σ ℚ} (h : fischer f f = 0) :
    f = 0 := by
  rw [fischer, sum_eq_zero_iff_of_nonneg fun m _ => by
    have : (0 : ℚ) ≤ f.coeff m * f.coeff m := mul_self_nonneg _
    positivity] at h
  ext m
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hm
  have h1 := h m (mem_support_iff.mpr hm)
  have h2 : ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  exact hm (mul_self_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right h2))

/-- `h_1(X) = tr X`: both have Fock norm `N` and pair to `N` (`⟨tr X, h_1⟩ = ⟨1, Δ h_1⟩`), so
their difference has norm `0`. -/
theorem hX_one : hX N 1 = trX N := by
  have h11 : fischer (hX N 1) (hX N 1) = N := by rw [fischer_hX]; norm_num [Nat.ascFactorial]
  have htt : fischer (trX N) (trX N) = N := by simpa using fischer_trX_pow (N := N) 1
  have ht1 : fischer (trX N) (hX N 1) = N := by
    have := fischer_trX_mul (N := N) 1 (hX N 1)
    rw [mul_one, trD_hX, hX_zero, smul_eq_C_mul, fischer_C_mul_right, fischer_one_one] at this
    simpa using this
  have ht1' : fischer (hX N 1) (trX N) = N := by rw [fischer_comm]; exact ht1
  rw [← sub_eq_zero]
  refine eq_zero_of_fischer_self ?_
  rw [fischer_sub_left, fischer_sub_right, fischer_sub_right, h11, htt, ht1, ht1']
  ring

theorem sX_two_one : sX N ![2, 1] = trX N * hX N 2 - hX N 3 := by
  rw [sX, Matrix.det_fin_two]
  simp [hZ, hX_zero, hX_one]
  ring

/-- **The Fock norm of `s_{(2,1)}(X)` is `(N − 1) N (N + 1)`**, the content product of the shape
`(2, 1)` (contents `0, 1, −1`): the first shape that is neither a row nor a column. From
`trD_hX`, the adjointness of `tr X` and `Δ`, and the norms of the rows. -/
theorem fischer_sX_two_one :
    fischer (sX N ![2, 1]) (sX N ![2, 1]) = ((N : ℚ) - 1) * N * (N + 1) := by
  have h2 := fischer_hX (N := N) 2
  have h3 := fischer_hX (N := N) 3
  have ht := fischer_trX_pow (N := N) 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at ht
  have hD3 : trD N (hX N 3) = ((N : ℚ) + 2) • hX N 2 := by
    rw [trD_hX]; norm_num
  have hD2 : trD N (hX N 2) = ((N : ℚ) + 1) • trX N := by
    rw [trD_hX, hX_one]; norm_num
  have hDt : trD N (trX N) = C (N : ℚ) := by
    rw [← hX_one, trD_hX, hX_zero, smul_eq_C_mul, mul_one]; simp
  -- `⟨tr X · h₂, h₃⟩ = (N + 2) ‖h₂‖²`
  have e1 : fischer (trX N * hX N 2) (hX N 3) = ((N : ℚ) + 2) * fischer (hX N 2) (hX N 2) := by
    rw [fischer_trX_mul, hD3, smul_eq_C_mul, fischer_C_mul_right]
  -- `⟨h₂, (tr X)²⟩ = (N + 1) ‖tr X‖²`
  have e2 : fischer (hX N 2) (trX N * trX N) = ((N : ℚ) + 1) * fischer (trX N) (trX N) := by
    rw [fischer_comm, fischer_trX_mul, hD2, smul_eq_C_mul, fischer_C_mul_right]
  -- `Δ (tr X · h₂) = N h₂ + (N + 1) (tr X)²`
  have hD : trD N (trX N * hX N 2) = C (N : ℚ) * hX N 2 + C ((N : ℚ) + 1) * (trX N * trX N) := by
    rw [Derivation.leibniz, hDt, hD2, smul_eq_mul, smul_eq_mul, smul_eq_C_mul]
    ring
  have e3 : fischer (trX N * hX N 2) (trX N * hX N 2)
      = N * fischer (hX N 2) (hX N 2) + ((N : ℚ) + 1) * fischer (hX N 2) (trX N * trX N) := by
    rw [fischer_trX_mul, hD, fischer_add_right, fischer_C_mul_right, fischer_C_mul_right]
  rw [sX_two_one, fischer_sub_left, fischer_sub_right, fischer_sub_right, e3, e2, e1,
    fischer_comm (hX N 3), e1, h2, h3, ht]
  simp only [Nat.ascFactorial]
  push_cast
  ring

end RMT.Fock
