import RMTlib.Fock.Virasoro
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

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

end RMT.Fock.Virasoro
