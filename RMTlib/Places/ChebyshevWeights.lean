import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Log.Sum

/-!
# Chebyshev's identity and finite weights (RMTlib#169, lane ED)

The starting point of Chebyshev's and Diamond–Erdős's elementary bounds for `ψ`:

* `log_factorial_eq_sum_psi`: `log N! = ∑_{m ≤ N} ψ(N/m)` (Chebyshev's identity, from
  `Λ * ζ = log`);
* `sum_weight_log_factorial`: for finitely many weights `a_d`,
  `∑_d a_d log ⌊N/d⌋! = ∑_{m ≤ N} ψ(N/m) · (∑_{d ∣ m} a_d)`.

The kernel `m ↦ ∑_{d ∣ m} a_d` is what Chebyshev (weights `1, -1, -1, -1, 1` at `1, 2, 3, 5, 30`)
and Diamond–Erdős (arbitrarily sharp finite Möbius truncations) choose so that the left side is
`c · N + O(log N)` and the kernel is a step function with controlled partial sums. Mathlib-only.
-/

open Finset ArithmeticFunction
open scoped Nat Chebyshev ArithmeticFunction.zeta

namespace RMT.Places.ChebyshevWeights

/-- `ψ` at a natural argument, as a sum over `Ioc 0 n`. -/
noncomputable def Ψ (n : ℕ) : ℝ := ∑ k ∈ Ioc 0 n, vonMangoldt k

theorem psi_div_eq (N m : ℕ) : ψ ((N : ℝ) / m) = Ψ (N / m) := by
  rw [Chebyshev.psi, Ψ, Nat.floor_div_eq_div]

/-- Chebyshev's identity at natural arguments: `log N! = ∑_{m ≤ N} Ψ(N/m)`. -/
theorem log_factorial_eq_sum_Ψ (N : ℕ) : Real.log (N ! : ℕ) = ∑ m ∈ Ioc 0 N, Ψ (N / m) := by
  rw [← Real.sum_log_eq_log_factorial]
  have h := sum_Ioc_mul_eq_sum_sum (ζ : ArithmeticFunction ℝ) vonMangoldt N
  rw [zeta_mul_vonMangoldt] at h
  simp only [log_apply] at h
  rw [h]
  refine sum_congr rfl fun m hm => ?_
  rw [natCoe_apply, zeta_apply, ite_eq_right (by simp at hm; omega), Nat.cast_one, one_mul, Ψ]

/-- **Chebyshev's identity**: `log N! = ∑_{m ≤ N} ψ(N/m)`. -/
theorem log_factorial_eq_sum_psi (N : ℕ) :
    Real.log (N ! : ℕ) = ∑ m ∈ Ioc 0 N, ψ ((N : ℝ) / m) := by
  rw [log_factorial_eq_sum_Ψ]
  exact sum_congr rfl fun m _ => (psi_div_eq N m).symm

/-- **Finite weights.** For weights `a` on a finite set `S` of positive integers,
`∑_{d ∈ S} a_d log ⌊N/d⌋! = ∑_{m ≤ N} Ψ(N/m) · ∑_{d ∈ S, d ∣ m} a_d`. -/
theorem sum_weight_log_factorial (S : Finset ℕ) (hS : ∀ d ∈ S, 0 < d) (a : ℕ → ℝ) (N : ℕ) :
    ∑ d ∈ S, a d * Real.log ((N / d) ! : ℕ) =
      ∑ m ∈ Ioc 0 N, Ψ (N / m) * ∑ d ∈ S with d ∣ m, a d := by
  simp_rw [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hd0 := hS d hd
  rw [log_factorial_eq_sum_Ψ, mul_sum]
  -- the multiples `m = d * m'` of `d` in `Ioc 0 N` are the images of `m' ∈ Ioc 0 (N / d)`
  rw [← sum_filter]
  symm
  refine sum_nbij' (fun m => m / d) (fun m' => d * m') ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [mem_filter, mem_Ioc] at hm ⊢
    obtain ⟨⟨h0, hN⟩, ⟨c, rfl⟩⟩ := hm
    rw [Nat.mul_div_cancel_left _ hd0]
    refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h0), ?_⟩
    exact (Nat.le_div_iff_mul_le hd0).mpr (by rw [mul_comm]; exact hN)
  · intro m' hm'
    simp only [mem_filter, mem_Ioc] at hm' ⊢
    refine ⟨⟨Nat.mul_pos hd0 hm'.1, ?_⟩, dvd_mul_right d m'⟩
    have := (Nat.le_div_iff_mul_le hd0).mp hm'.2
    rw [mul_comm]; exact this
  · intro m hm
    simp only [mem_filter] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro m' _
    exact Nat.mul_div_cancel_left m' hd0
  · intro m hm
    simp only [mem_filter] at hm
    obtain ⟨c, rfl⟩ := hm.2
    rw [Nat.mul_div_cancel_left _ hd0, Nat.div_div_eq_div_mul, mul_comm (Ψ _)]

/-- The same with `ψ` at real arguments. -/
theorem sum_weight_log_factorial_psi (S : Finset ℕ) (hS : ∀ d ∈ S, 0 < d) (a : ℕ → ℝ) (N : ℕ) :
    ∑ d ∈ S, a d * Real.log ((N / d) ! : ℕ) =
      ∑ m ∈ Ioc 0 N, ψ ((N : ℝ) / m) * ∑ d ∈ S with d ∣ m, a d := by
  rw [sum_weight_log_factorial S hS]
  exact sum_congr rfl fun m _ => by rw [psi_div_eq]

end RMT.Places.ChebyshevWeights
