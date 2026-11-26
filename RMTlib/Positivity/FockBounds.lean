import RMTlib.Fock.Fischer
import MeaningLib.Frame.Pattern

/-!
# Node-4 positivity patterns: Fock norm bounds

RMTlib#36 item A1 (Alpöge's `GlobalTheory.FockNormBound.fock_norm_bounds`). For the Fischer form
`⟨f, g⟩ = Σ_m f_m g_m m!` (`RMT.Fock.fischer`, diagonal on monomials with `‖x^m‖² = m!`):

* `coeff_X_mul_pderiv`: the number operator `X_v ∂_v` scales `x^m` by `m_v`.
* `fischer_pderiv_self`: `‖∂_v P‖² = ⟨P, X_v ∂_v P⟩ = Σ_m m_v P_m² m!`.
* `fischer_pderiv_le` (**A1, `∂`**): `‖∂_v P‖² ≤ d ‖P‖²` when every monomial of `P` has `x_v`-degree
  at most `d` (in particular when `deg P ≤ d`).
* `fischer_X_mul_self`: `‖X_v P‖² = ‖P‖² + ‖∂_v P‖²` (the canonical commutation relation).
* `fischer_X_mul_le` (**A1, `X`**): `‖X_v P‖² ≤ (d + 1) ‖P‖²` under the same hypothesis.

Both bounds are tagged `@[frame_pattern]`. The proof's form is a `ℂ`-hermitian Fischer product; the
`ℚ`-bilinear form here is its real part on rational polynomials, and an `IsFockIP` interface for
hermitian embeddings is the next step.
-/

namespace RMT.Fock

open MvPolynomial Finset

variable {σ : Type*} [DecidableEq σ]

/-- The number operator `X_v ∂_v` scales the coefficient of `x^m` by `m_v`. -/
theorem coeff_X_mul_pderiv (v : σ) (P : MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    (X v * pderiv v P).coeff m = (m v : ℚ) * P.coeff m := by
  rw [coeff_X_mul']
  split_ifs with h
  · rw [coeff_pderiv]
    have hv : 1 ≤ m v := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
    have hm : m - Finsupp.single v 1 + Finsupp.single v 1 = m := by
      ext w
      by_cases hw : w = v
      · subst hw; simp; omega
      · simp [Ne.symm hw]
    rw [hm]
    have : (((m - Finsupp.single v 1 : σ →₀ ℕ) v : ℕ) : ℚ) + 1 = m v := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      push_cast [hv]
      ring
    rw [this, mul_comm]
  · have : m v = 0 := Finsupp.notMem_support_iff.mp h
    simp [this]

/-- `‖∂_v P‖² = Σ_m m_v P_m² m!`. -/
theorem fischer_pderiv_self (v : σ) (P : MvPolynomial σ ℚ) :
    fischer (pderiv v P) (pderiv v P) =
      ∑ m ∈ P.support, (m v : ℚ) * P.coeff m * P.coeff m *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  rw [← fischer_X_mul_left, fischer_comm, fischer]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_X_mul_pderiv]
  ring

/-- **A1, `∂`**: `‖∂_v P‖² ≤ d ‖P‖²` when every monomial of `P` has `x_v`-degree at most `d`. -/
@[frame_pattern]
theorem fischer_pderiv_le (v : σ) (P : MvPolynomial σ ℚ) (d : ℕ)
    (hd : ∀ m ∈ P.support, m v ≤ d) :
    fischer (pderiv v P) (pderiv v P) ≤ d * fischer P P := by
  rw [fischer_pderiv_self, fischer, mul_sum]
  refine sum_le_sum fun m hm => ?_
  have hfac : (0 : ℚ) ≤ ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by positivity
  have hsq : 0 ≤ P.coeff m * P.coeff m := mul_self_nonneg _
  have hmv : (m v : ℚ) ≤ d := by exact_mod_cast hd m hm
  calc (m v : ℚ) * P.coeff m * P.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ)
      = (m v : ℚ) * (P.coeff m * P.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ)) := by
        ring
    _ ≤ d * (P.coeff m * P.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ)) := by
        gcongr

/-- `‖X_v P‖² = ‖P‖² + ‖∂_v P‖²` (`[∂_v, X_v] = 1`). -/
theorem fischer_X_mul_self (v : σ) (P : MvPolynomial σ ℚ) :
    fischer (X v * P) (X v * P) = fischer P P + fischer (pderiv v P) (pderiv v P) := by
  rw [fischer_X_mul_left, Derivation.leibniz, pderiv_X_self, smul_eq_mul, smul_eq_mul, mul_one,
    fischer_add_right, ← fischer_X_mul_left, fischer_comm (X v * pderiv v P), add_comm]

/-- **A1, `X`**: `‖X_v P‖² ≤ (d + 1) ‖P‖²` when every monomial of `P` has `x_v`-degree at most `d`. -/
@[frame_pattern]
theorem fischer_X_mul_le (v : σ) (P : MvPolynomial σ ℚ) (d : ℕ)
    (hd : ∀ m ∈ P.support, m v ≤ d) :
    fischer (X v * P) (X v * P) ≤ (d + 1) * fischer P P := by
  rw [fischer_X_mul_self]
  have := fischer_pderiv_le v P d hd
  linarith

end RMT.Fock
