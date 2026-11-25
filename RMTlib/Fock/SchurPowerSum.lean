import RMTlib.Fock.Virasoro
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import RMTlib.Symmetric.DualJacobiTrudi
import RMTlib.Fock.Laplacian

/-!
# Elementary symmetric functions in the power-sum model

Stage 1 of RMTlib#5 item 1 (Schur functions in the power-sum model `Λ = ℚ[p_1, p_2, …]`, which
blocks the BDTW patterns of RMTlib#19). The elementary symmetric functions are defined in `Λ` by
Newton's recursion,

  `k e_k = Σ_{i < k} (−1)^{k − 1 − i} e_i p_{k − i}`,

and `ev_eP` shows that in `N` variables (`p_k ↦ Σ_j x_j^k`, `RMT.Fock.Virasoro.ev`) they are
Mathlib's `esymm`, by Mathlib's Newton identities (`MvPolynomial.mul_esymm_eq_sum`).

Schur functions are then built from the `e_k` (dual Jacobi–Trudi), i.e. through the fermionic side
and its Pauli wall `e_k = 0` for `k > N` (`RMT.Symmetric.Wall`).
-/

open MvPolynomial Finset

namespace RMT.Fock.Virasoro

/-- **`e_k` in the power-sum model**, by Newton's recursion
`e_{k+1} = (−1)^{k+2}/(k+1) · Σ_{i ≤ k} (−1)^i e_i p_{k+1−i}`. -/
noncomputable def eP : ℕ → Λ
  | 0 => 1
  | k + 1 => (((k + 1 : ℕ) : ℚ)⁻¹ * (-1) ^ (k + 2)) •
      ∑ i : Fin (k + 1), ((-1 : ℚ) ^ (i : ℕ)) • (eP i * X (k + 1 - i))
decreasing_by exact i.isLt

theorem eP_zero : eP 0 = 1 := by rw [eP]

/-- The sum over `antidiagonal n` with first coordinate `< n`, as a sum over `Fin n`. -/
theorem sum_antidiagonal_lt {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → ℕ → M) :
    ∑ a ∈ antidiagonal n with a.1 < n, f a.1 a.2 = ∑ i : Fin n, f i (n - i) := by
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    if_neg (lt_irrefl n), add_zero, ← Finset.sum_range (fun i => f i (n - i))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [if_pos (Finset.mem_range.mp hi)]

/-- **In `N` variables `eP` is `esymm`**, by Newton's identities. -/
theorem ev_eP (N : ℕ) (k : ℕ) : ev N (eP k) = esymm (Fin N) ℚ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · simp [eP_zero]
    have hN := MvPolynomial.mul_esymm_eq_sum (Fin N) ℚ (k + 1)
    rw [sum_antidiagonal_lt (k + 1) fun a b => (-1 : MvPolynomial (Fin N) ℚ) ^ a *
      esymm (Fin N) ℚ a * psum (Fin N) ℚ b] at hN
    rw [eP, map_smul, map_sum]
    have hsum : ∑ i : Fin (k + 1), ev N (((-1 : ℚ) ^ (i : ℕ)) • (eP i * X (k + 1 - i))) =
        ∑ i : Fin (k + 1), (-1 : MvPolynomial (Fin N) ℚ) ^ (i : ℕ) * esymm (Fin N) ℚ i *
          psum (Fin N) ℚ (k + 1 - i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_mul, ih i i.isLt]
      simp only [ev, aeval_X, smul_eq_C_mul, map_pow, map_neg, map_one]
      ring
    rw [hsum]
    set S := ∑ i : Fin (k + 1), (-1 : MvPolynomial (Fin N) ℚ) ^ (i : ℕ) * esymm (Fin N) ℚ i *
      psum (Fin N) ℚ (k + 1 - i) with hSdef
    set u : MvPolynomial (Fin N) ℚ := (-1) ^ (k + 2) with hu
    have h1 : u * u = 1 := by rw [hu, ← pow_add, show k + 2 + (k + 2) = 2 * (k + 2) by ring, pow_mul]; simp
    have hN' : ((k + 1 : ℕ) : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ (k + 1) = u * S := by
      rw [hN, hu]
    have hS : S = u * (C ((k + 1 : ℕ) : ℚ) * esymm (Fin N) ℚ (k + 1)) := by
      rw [← map_natCast (C : ℚ →+* MvPolynomial (Fin N) ℚ)] at hN'
      linear_combination (-u) * hN' + (-S) * h1
    have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [hS, smul_eq_C_mul, map_mul, map_pow, map_neg, map_one, ← hu]
    calc C ((k + 1 : ℕ) : ℚ)⁻¹ * u * (u * (C ((k + 1 : ℕ) : ℚ) * esymm (Fin N) ℚ (k + 1)))
        = (C ((k + 1 : ℕ) : ℚ)⁻¹ * C ((k + 1 : ℕ) : ℚ)) * (u * u) * esymm (Fin N) ℚ (k + 1) := by
          ring
      _ = esymm (Fin N) ℚ (k + 1) := by
          rw [h1, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul, one_mul]

/-! ## Schur functions in the power-sum model, by dual Jacobi–Trudi -/

/-- `e_k` in `Λ` with an integer index (`0` for `k < 0`). -/
noncomputable def eZP (k : ℤ) : Λ := if 0 ≤ k then eP k.toNat else 0

/-- `det (e_{x_i − i + j})_{i, j < N}` in `Λ`. -/
noncomputable def eDetP {N : ℕ} (x : Fin N → ℤ) : Λ :=
  Matrix.det (Matrix.of fun i j : Fin N => eZP (x i - i + j))

/-- **The Schur function `s_μ` in the power-sum model**, by dual Jacobi–Trudi with `N` columns
(`N` any bound on the parts of `μ`; see `ptEval_sP`). -/
noncomputable def sP {K : ℕ} (N : ℕ) (mu : Fin K → ℕ) : Λ :=
  eDetP (fun i : Fin N => (RMT.Symmetric.conjV N mu i : ℤ))

/-- Evaluation of `Λ` at the point `(a_0, …, a_{m−1})`: `p_k ↦ Σ_{j < m} a_j^k`. -/
noncomputable def ptEval (a : ℕ → ℚ) (m : ℕ) : Λ →ₐ[ℚ] ℚ :=
  (aeval fun j : Fin m => a j).comp (ev m)

theorem ptEval_eP (a : ℕ → ℚ) (m k : ℕ) : ptEval a m (eP k) = RMT.Symmetric.eV a m k := by
  simp only [ptEval, AlgHom.comp_apply, ev_eP, esymm, map_sum, map_prod, aeval_X,
    RMT.Symmetric.eV]

theorem ptEval_eZP (a : ℕ → ℚ) (m : ℕ) (k : ℤ) :
    ptEval a m (eZP k) = RMT.Symmetric.eZ a m k := by
  unfold eZP RMT.Symmetric.eZ
  split_ifs <;> simp [ptEval_eP]

theorem ptEval_eDetP (a : ℕ → ℚ) (m : ℕ) {N : ℕ} (x : Fin N → ℤ) :
    ptEval a m (eDetP x) = RMT.Symmetric.eDet a m x := by
  rw [eDetP, AlgHom.map_det, RMT.Symmetric.eDet]
  congr 1
  ext i j
  simp [ptEval_eZP]

/-- **`sP` is the Schur function**: at any point with `m` variables it evaluates to RMTlib's
tableau Schur polynomial `schurV`, for every bound `N` on the parts. -/
theorem ptEval_sP (a : ℕ → ℚ) (m : ℕ) {K N : ℕ} {mu : Fin K → ℕ} (hm : Antitone mu)
    (hN : ∀ j, mu j ≤ N) : ptEval a m (sP N mu) = RMT.Symmetric.schurV a K m mu := by
  rw [sP, ptEval_eDetP, RMT.Symmetric.schurV_eq_eDet_conjV a m hm hN]

/-! ## `L_1` on the `e_k` -/

theorem neg_one_pow_mul_neg_one_pow (k i : ℕ) (hi : i ≤ k) :
    ((-1 : ℚ) ^ (k + 2)) * (-1) ^ i = (-1) ^ (k - i) := by
  rw [← pow_add, show k + 2 + i = (k - i) + 2 * (i + 1) by omega, pow_add, pow_mul]
  simp

/-- **Newton's recursion**, as a sum over `range`:
`(k + 1) e_{k+1} = Σ_{i ≤ k} (−1)^{k − i} e_i p_{k+1−i}`. -/
theorem eP_rec (k : ℕ) : (((k + 1 : ℕ) : ℚ)) • eP (k + 1) =
    ∑ i ∈ range (k + 1), ((-1 : ℚ) ^ (k - i)) • (eP i * X (k + 1 - i)) := by
  rw [eP, smul_smul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, Finset.smul_sum,
    Fin.sum_univ_eq_sum_range
      (fun i => ((-1 : ℚ) ^ (k + 2)) • ((-1 : ℚ) ^ i) • (eP i * X (k + 1 - i))) (k + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_smul, neg_one_pow_mul_neg_one_pow k i (by simpa [Nat.lt_succ_iff] using hi)]

theorem L1_eP_zero (a : ℚ) : L1 a (eP 0) = 0 := by rw [eP_zero, Derivation.map_one_eq_zero]

/-- **`L_1` lowers `e_k` with weight `a − k + 1`**: `L_1^{(a)} e_{k+1} = (a − k) e_k`. At charge
`a = N` this is `Σ_i ∂_{x_i} e_{k+1} = (N − k) e_k` (`ev_L1`). -/
theorem L1_eP (a : ℚ) (k : ℕ) : L1 a (eP (k + 1)) = (a - k) • eP k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hk1 : (((k + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
    refine smul_right_injective Λ hk1 ?_
    simp only
    rw [← (L1 a).map_smul, eP_rec, map_sum]
    have hterm : ∀ i ∈ range (k + 1), L1 a (((-1 : ℚ) ^ (k - i)) • (eP i * X (k + 1 - i))) =
        ((-1 : ℚ) ^ (k - i)) • (L1 a (eP i) * X (k + 1 - i)) +
          ((-1 : ℚ) ^ (k - i)) • (eP i * L1 a (X (k + 1 - i))) := by
      intro i _
      rw [(L1 a).map_smul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_add, add_comm,
        mul_comm (X _)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun i => ((-1 : ℚ) ^ (k - i)) • (L1 a (eP i) * X (k + 1 - i))),
      L1_eP_zero, zero_mul, smul_zero, add_zero]
    have hA : ∑ j ∈ range k, ((-1 : ℚ) ^ (k - (j + 1))) • (L1 a (eP (j + 1)) * X (k + 1 - (j + 1))) =
        ∑ j ∈ range k, ((-1 : ℚ) ^ (k - 1 - j) * (a - j)) • (eP j * X (k - j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk := Finset.mem_range.mp hj
      rw [ih j hjk, smul_mul_assoc, smul_smul, show k - (j + 1) = k - 1 - j by omega,
        show k + 1 - (j + 1) = k - j by omega]
    rw [Finset.sum_range_succ (fun i => ((-1 : ℚ) ^ (k - i)) • (eP i * L1 a (X (k + 1 - i)))),
      Nat.sub_self, pow_zero, one_smul, show k + 1 - k = 1 by omega, L1_X_one]
    have hB : ∑ i ∈ range k, ((-1 : ℚ) ^ (k - i)) • (eP i * L1 a (X (k + 1 - i))) =
        ∑ j ∈ range k, (-(-1 : ℚ) ^ (k - 1 - j) * ((k : ℚ) + 1 - j)) • (eP j * X (k - j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk := Finset.mem_range.mp hj
      rw [show k + 1 - j = (k - j - 1) + 2 by omega, L1_X]
      simp only [show k - j - 1 + 2 ≠ 0 by omega, if_false, pc,
        show k - j - 1 + 2 - 1 = k - j by omega, show k - j ≠ 0 by omega]
      rw [mul_smul_comm, smul_smul, show k - j = (k - 1 - j) + 1 by omega, pow_succ]
      congr 1
      have hc : (((k - 1 - j + 1 - 1 + 2 : ℕ)) : ℚ) = (k : ℚ) + 1 - j := by
        rw [show k - 1 - j + 1 - 1 + 2 = (k + 1) - j by omega, Nat.cast_sub (by omega)]
        push_cast; ring
      rw [hc]
      ring
    rw [hA, hB, ← add_assoc, ← Finset.sum_add_distrib]
    have hC : ∑ j ∈ range k, (((-1 : ℚ) ^ (k - 1 - j) * (a - j)) • (eP j * X (k - j)) +
        (-(-1 : ℚ) ^ (k - 1 - j) * ((k : ℚ) + 1 - j)) • (eP j * X (k - j))) =
        (a - k - 1) • ∑ j ∈ range k, ((-1 : ℚ) ^ (k - 1 - j)) • (eP j * X (k - j)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← add_smul, smul_smul]
      congr 1
      ring
    rw [hC, mul_comm (eP k), ← smul_eq_C_mul]
    rcases k with _ | k
    · simp
    · have hrec := eP_rec k
      have hsum : ∑ j ∈ range (k + 1), ((-1 : ℚ) ^ (k + 1 - 1 - j)) • (eP j * X (k + 1 - j)) =
          (((k + 1 : ℕ) : ℚ)) • eP (k + 1) := by
        rw [hrec]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show k + 1 - 1 - j = k - j by omega]
      rw [hsum, smul_smul, smul_smul, ← add_smul]
      congr 1
      push_cast
      ring

/-! ## `L_1` on the dual Jacobi–Trudi determinants: one box removed, weight `a + c` -/

/-- `L_1^{(a)} e_k = (a − k + 1) e_{k−1}` for every integer `k`. -/
theorem L1_eZP (a : ℚ) (k : ℤ) : L1 a (eZP k) = (a - k + 1) • eZP (k - 1) := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have h1 : eZP k = 0 := by rw [eZP, if_neg (by omega)]
    have h2 : eZP (k - 1) = 0 := by rw [eZP, if_neg (by omega)]
    rw [h1, h2, map_zero, smul_zero]
  · have h1 : eZP 0 = 1 := by simp [eZP, eP_zero]
    have h2 : eZP (0 - 1) = 0 := by simp [eZP]
    rw [h1, h2, Derivation.map_one_eq_zero, smul_zero]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    have h1 : eZP ((n : ℤ) + 1) = eP (n + 1) := by
      simp only [eZP, show (0 : ℤ) ≤ n + 1 by omega, if_true]
      congr 1
    have h2 : eZP ((n : ℤ) + 1 - 1) = eP n := by simp [eZP]
    rw [h1, h2, L1_eP]
    congr 1
    push_cast
    ring

/-- The row `j ↦ j · e_{x_i − i + j − 1}` is row `i` of `A C`, `C_{j−1, j} = j`. -/
theorem shiftP_row_eq {l : ℕ} (x : Fin l → ℤ) (i j : Fin l) :
    ((j : ℕ) : Λ) * eZP (x i - i + j - 1)
      = ((Matrix.of fun i j : Fin l => eZP (x i - i + j) : Matrix (Fin l) (Fin l) Λ) *
          (Matrix.of fun a b : Fin l => if (a : ℕ) + 1 = b then ((b : ℕ) : Λ) else 0 :
            Matrix (Fin l) (Fin l) Λ)) i j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, mul_ite, mul_zero]
  by_cases hj : (j : ℕ) = 0
  · rw [hj, Nat.cast_zero, zero_mul]
    refine (sum_eq_zero fun a _ => if_neg (by omega)).symm
  · have hlt : (j : ℕ) - 1 < l := by omega
    rw [sum_eq_single ⟨(j : ℕ) - 1, hlt⟩]
    · rw [if_pos (by simp; omega), mul_comm]
      congr 2
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj)]
      ring
    · intro a _ ha
      rw [if_neg]
      intro h
      apply ha
      ext
      simp only
      omega
    · simp

/-- **`L_1` on a dual Jacobi–Trudi determinant**: for every integer vector `x`,
`L_1^{(a)} det (e_{x_i − i + j}) = Σ_i (a − x_i + i + 1) · det (e_{x' − i + j})` with `x' = x − e_i`.
For `x = μ′` (`sP`), lowering column `i` removes the box `(μ′_i − 1, i)`, of content
`c = i − μ′_i + 1`, so the weight is `a + c`: at `a = N` this is `Σ_i ∂_{x_i} s_μ = Σ (N + c) s_{μ − □}`
(RMTlib#5 item 1). Proved like `RMT.Fock.trD_sX`: the `−j` part of each differentiated row is a row
of `A C` with `tr C = 0`. -/
theorem L1_eDetP (a : ℚ) {l : ℕ} (x : Fin l → ℤ) :
    L1 a (eDetP x) = ∑ i : Fin l, (a - x i + i + 1) • eDetP (Function.update x i (x i - 1)) := by
  classical
  set A : Matrix (Fin l) (Fin l) Λ := Matrix.of fun i j : Fin l => eZP (x i - i + j)
  set Cm : Matrix (Fin l) (Fin l) Λ :=
    Matrix.of fun a b : Fin l => if (a : ℕ) + 1 = b then ((b : ℕ) : Λ) else 0
  have hrow : ∀ i : Fin l, (fun j => L1 a (A i j))
      = (C (a - x i + i + 1) : Λ) • (fun j : Fin l => eZP (x i - 1 - i + j)) +
          (-1 : Λ) • (A * Cm) i := by
    intro i
    funext j
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      ← shiftP_row_eq x i j]
    simp only [A, Matrix.of_apply, L1_eZP]
    rw [show x i - 1 - (i : ℤ) + j = x i - i + j - 1 by ring, smul_eq_C_mul]
    rw [← map_natCast (C : ℚ →+* Λ)]
    rw [show (-1 : Λ) * (C ((j : ℕ) : ℚ) * eZP (x i - i + j - 1)) =
      C (-((j : ℕ) : ℚ)) * eZP (x i - i + j - 1) by simp [map_neg]]
    rw [← add_mul, ← map_add]
    congr 2
    push_cast
    ring
  have hupd : ∀ i : Fin l, A.updateRow i (fun j : Fin l => eZP (x i - 1 - i + j))
      = Matrix.of fun i' j : Fin l => eZP (Function.update x i (x i - 1) i' - i' + j) := by
    intro i
    ext i' j
    by_cases h : i' = i
    · subst h
      simp
    · simp [A, Matrix.updateRow_ne h, Function.update_of_ne h]
  rw [show eDetP x = A.det from rfl, RMT.Fock.derivation_det]
  simp_rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, hupd]
  rw [sum_add_distrib, ← mul_sum, RMT.Fock.sum_det_updateRow_mul]
  have htr : Cm.trace = 0 := by
    refine sum_eq_zero fun j _ => ?_
    simp [Cm]
  rw [htr, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul]
  rfl

end RMT.Fock.Virasoro
