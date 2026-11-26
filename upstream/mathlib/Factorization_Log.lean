/-
Copyright (c) 2026 <contributor>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <contributor>
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The logarithm of a natural number as a sum over its prime factorization

* `Real.log_natCast_eq_sum_factorization`: `log n = ∑ p ∈ n.primeFactors, n.factorization p * log p`.
* `Real.sum_factorization_mul_log_le`: the truncated product formula. Over any finite set `s` of
  natural numbers, `∑ p ∈ s, n.factorization p * log p ≤ log n`.
* `Real.sum_padicValNat_mul_log_le`: the same with `padicValNat`, over a finite set of primes, with
  the bound relaxed to `log b` for any `b ≥ n`.
-/

open Finset

namespace Real

/-- The logarithm of a natural number is the sum of `log p` weighted by the `p`-adic valuation. -/
theorem log_natCast_eq_sum_factorization (n : ℕ) :
    log n = ∑ p ∈ n.primeFactors, n.factorization p * log p := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.cast_prod, log_prod]
  · simp [Nat.support_factorization]
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity

/-- **The truncated product formula**: over any finite set of natural numbers,
`∑ p ∈ s, n.factorization p * log p ≤ log n`. Non-primes contribute nothing. -/
theorem sum_factorization_mul_log_le (n : ℕ) (s : Finset ℕ) :
    ∑ p ∈ s, n.factorization p * log p ≤ log n := by
  classical
  rw [log_natCast_eq_sum_factorization, ← sum_filter_add_sum_filter_not s (· ∈ n.primeFactors)]
  have h0 : ∑ p ∈ s.filter (· ∉ n.primeFactors), (n.factorization p : ℝ) * log p = 0 :=
    sum_eq_zero fun p hp => by
      have h := (mem_filter.mp hp).2
      rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at h
      simp [h]
  rw [h0, add_zero]
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_filter.mp hp).2) fun p hp _ => ?_
  have := (Nat.prime_of_mem_primeFactors hp).one_lt
  exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by exact_mod_cast this.le))

/-- The truncated product formula with `padicValNat`, over a finite set of primes, bounded by
`log b` for any `b ≥ n`. -/
theorem sum_padicValNat_mul_log_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) {n b : ℕ}
    (hnb : n ≤ b) : ∑ p ∈ s, (padicValNat p n : ℝ) * log p ≤ log b := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [padicValNat] using log_natCast_nonneg b
  calc ∑ p ∈ s, (padicValNat p n : ℝ) * log p
      = ∑ p ∈ s, n.factorization p * log p :=
        sum_congr rfl fun p hp => by rw [Nat.factorization_def n (hs p hp), Nat.padicValNat_def]
    _ ≤ log n := sum_factorization_mul_log_le n s
    _ ≤ log b := log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn) (by exact_mod_cast hnb)

end Real
