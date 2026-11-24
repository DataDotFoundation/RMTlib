import Mathlib

/-!
# The Keating–Snaith leading constant

For the characteristic polynomial `Z_N` of a Haar-random `N × N` unitary matrix, Keating and
Snaith (2000) showed `𝔼|Z_N(1)|^{2k} ~ (G(1+k)² / G(1+2k)) · N^{k²}`, with `G` Barnes'
G-function. For integer `k` the constant is the finite product

  `G(1+k)² / G(1+2k) = ∏_{j<k} j! / (j+k)!`,

which is `ksConst k` below. By the hook-length formula it is also `g_k / (k²)!`, where `g_k`
counts the standard Young tableaux of the `k × k` square (see `RMTlib.Tableaux.Square`).

## Main results
* `RMT.ksConst_pos`, `RMT.ksConst_eq_div`: positivity and the quotient form.
* `RMT.ksConst_zero` … `RMT.ksConst_three`: `1, 1, 1/12, 1/8640`.
* `RMT.ksConst_eq_inv_mutual`: the constant is the mutual energy of two adjacent strings of
  length `k` (`bridge/links/tower-charges.md` §1, identity 2 with `d = σ = k`, `δ = 0`):
  `ksConst k = 1 / ∏_{a<k} ∏_{b<k} (k + b − a)`, the product of `y − x` over `x ∈ {0..k−1}`,
  `y ∈ {k..2k−1}` (`toy_examples/docs/hall-shifted.md`).
-/

open Finset
open scoped Nat

namespace RMT

/-- The Keating–Snaith constant `G(1+k)²/G(1+2k) = ∏_{j<k} j!/(j+k)!`. -/
def ksConst (k : ℕ) : ℚ := ∏ j ∈ range k, ((j ! : ℕ) : ℚ) / (((j + k) ! : ℕ) : ℚ)

theorem ksConst_pos (k : ℕ) : 0 < ksConst k :=
  prod_pos fun j _ => div_pos (by exact_mod_cast j.factorial_pos)
    (by exact_mod_cast (j + k).factorial_pos)

/-- The constant as a quotient of two superfactorial-type products. -/
theorem ksConst_eq_div (k : ℕ) :
    ksConst k = (∏ j ∈ range k, ((j ! : ℕ) : ℚ)) / ∏ j ∈ range k, (((j + k) ! : ℕ) : ℚ) :=
  prod_div_distrib _ _

theorem ksConst_zero : ksConst 0 = 1 := by simp [ksConst]

theorem ksConst_one : ksConst 1 = 1 := by simp [ksConst]

theorem ksConst_two : ksConst 2 = 1 / 12 := by
  simp [ksConst, prod_range_succ, Nat.factorial]; norm_num

theorem ksConst_three : ksConst 3 = 1 / 8640 := by
  simp [ksConst, prod_range_succ, Nat.factorial]; norm_num

/-- One row of the mutual product: `∏_{b<k} (j + 1 + b) = (j + k)! / j!`. -/
theorem prod_row_mutual (j k : ℕ) :
    ((j ! : ℕ) : ℚ) * ∏ b ∈ range k, ((j + 1 + b : ℕ) : ℚ) = (((j + k) ! : ℕ) : ℚ) := by
  rw [← Nat.factorial_mul_ascFactorial j k, Nat.ascFactorial_eq_prod_range]
  push_cast
  rfl

/-- **The Keating–Snaith constant is the mutual energy of two adjacent strings**:
`G(1+k)²/G(1+2k) = 1/∏_{x∈A, y∈B} (y − x)` with `A = {0, …, k−1}`, `B = {k, …, 2k−1}`. -/
theorem ksConst_eq_inv_mutual (k : ℕ) :
    ksConst k = 1 / ∏ a ∈ range k, ∏ b ∈ range k, ((k + b - a : ℕ) : ℚ) := by
  rw [← prod_range_reflect (fun a => ∏ b ∈ range k, ((k + b - a : ℕ) : ℚ)) k, one_div,
    ← prod_inv_distrib]
  unfold ksConst
  refine prod_congr rfl fun j hj => ?_
  have hj' : j < k := mem_range.mp hj
  have hrow : ∏ b ∈ range k, ((k + b - (k - 1 - j) : ℕ) : ℚ)
      = ∏ b ∈ range k, ((j + 1 + b : ℕ) : ℚ) :=
    prod_congr rfl fun b _ => by congr 1; omega
  rw [hrow]
  have hf : (0 : ℚ) < ((j ! : ℕ) : ℚ) := by exact_mod_cast j.factorial_pos
  rw [← prod_row_mutual j k, mul_comm, div_mul_cancel_right₀ hf.ne']

end RMT
