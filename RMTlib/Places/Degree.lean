import RMTlib.Places.Transfer
import RMTlib.Places.TowerPlaces

/-!
# The product formula as an Arakelov degree (MeaningLib#68 R4)

An **Arakelov divisor** over `ℚ` puts an integer `D p` at each prime and a real number `D∞` at the
place at `∞`. Its **degree** is `Σ_p D p · log p + D∞`: the sum over *all* places, `∞` included, each
weighted by its own `log` of the norm. The product formula is the statement that a **principal**
divisor has degree zero: for `n ≠ 0`, the divisor with `v_p(n)` at each `p` and `−log |n|` at `∞`.

This is the place-uniform form RH-Dual's divisor site uses (the proof's `mu`, "the sum over places").
`RMT.Transfer.log_eq_sum` is the same fact with `∞` moved to the other side. The degree is the
`degree` role of the places frame (`RMT.Frames.places`).

* `degOn S D Dinf`: the degree, summing the finite part over a finite set `S` of primes;
* `deg_principal`: **principal divisors have degree zero**, over any set of primes `S` containing
  the prime factors of `n`;
* `degOn_principal_le`: truncating the finite part to fewer primes can only make the degree of
  a principal divisor more negative (the inequality form, `sum_log_mul_padicValInt_le`).
-/

namespace RMT.Places

open Finset

/-- The Arakelov degree `Σ_{p ∈ S} D p · log p + D∞`. -/
noncomputable def degOn (S : Finset ℕ) (D : ℕ → ℤ) (Dinf : ℝ) : ℝ :=
  (∑ p ∈ S, (D p : ℝ) * Real.log p) + Dinf

/-- **The product formula as a degree**: the principal divisor of `n ≠ 0` (valuation `v_p(n)` at
each prime, `−log |n|` at `∞`) has degree zero, summed over any set of primes containing the prime
factors of `n`. -/
@[frame_transfer inf_p]
theorem deg_principal {n : ℤ} (hn : n ≠ 0) {S : Finset ℕ} (hS : n.natAbs.primeFactors ⊆ S)
    (hprime : ∀ q ∈ S, q.Prime) :
    degOn S (fun p => (padicValInt p n : ℤ)) (-Real.log |(n : ℝ)|) = 0 := by
  unfold degOn
  have h := RMT.StringInsertion.log_eq_sum_of_subset (Int.natAbs_ne_zero.mpr hn) hS hprime
  have habs : Real.log (n.natAbs : ℝ) = Real.log |(n : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [Int.cast_natCast, RMT.Transfer.padicValInt_eq_padicValNat_natAbs]
  rw [← habs, h]
  ring

/-- **Truncating the finite part** of a principal divisor to any set `S` of primes can only lower
its degree: `degOn S (div n) ≤ 0` (the inequality form in which the proof states the product
formula; cf. `RMT.Transfer.sum_log_mul_padicValInt_le`). -/
theorem degOn_principal_le {n : ℤ} (hn : n ≠ 0) {S : Finset ℕ} (hprime : ∀ q ∈ S, q.Prime) :
    degOn S (fun p => (padicValInt p n : ℤ)) (-Real.log |(n : ℝ)|) ≤ 0 := by
  have hS' : ∀ q ∈ S ∪ n.natAbs.primeFactors, q.Prime := by
    intro q hq
    rcases mem_union.mp hq with h | h
    · exact hprime q h
    · exact Nat.prime_of_mem_primeFactors h
  have h0 := deg_principal hn subset_union_right hS'
  unfold degOn at h0 ⊢
  have hle : ∑ p ∈ S, ((padicValInt p n : ℤ) : ℝ) * Real.log p ≤
      ∑ p ∈ S ∪ n.natAbs.primeFactors, ((padicValInt p n : ℤ) : ℝ) * Real.log p := by
    refine sum_le_sum_of_subset_of_nonneg subset_union_left fun q _ _ => ?_
    have : (0 : ℝ) ≤ Real.log q := Real.log_natCast_nonneg q
    positivity
  linarith

end RMT.Places
