import RMTlib.Places.HookValuation
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MeaningLib.Frame.Pattern

/-!
# Transfers between places, stated once

RMTlib#42 (from RH-Dual, at the user's direction): the moves RH-Dual keeps making by hand between a
random-matrix identity and a statement of Alpöge's proof, each stated generically with the
hypothesis that makes it sound.

**Transfer 1, value → homogeneous bound** (soundness: integrality). From an identity `Q · S = G` of
natural numbers (`G ≠ 0`):
* `Transfer.dvd`: `Q ∣ G` (at every prime at once);
* `Transfer.padicValNat_add`: `v_p Q + v_p S = v_p G` at every prime;
* `Transfer.le`: `Q ≤ G` (the size bound at `∞`).
It is lossless in the direction `Q · S = G ⇒ (divisibility, valuations, size)`; the slack is the
cofactor `S`, a statistic in its own right. Instance: `H(λ) · f^λ = |λ|!` (`hook_transfer`).

**Transfer 2, `∞ ↔ p` through integrality** (soundness: `Q` a nonzero natural):
* `Transfer.log_eq_sum`: `log Q = Σ_{p ∣ Q} v_p(Q) · log p` (the product formula), so a statement
  about the size of `Q` at `∞` and its `p`-profile are one statement.

They are tagged `@[frame_transfer value_bound]` / `inf_p` (MeaningLib PR #39), not `@[frame_pattern]`: their conclusions are fully generic. Matching them is bounded since MeaningLib PR #40 (reducible-transparency dischargers, per-attempt budgets); RMTlib's whole-library report guard checks it. The value-bound transfers declare their defining premise `h : Q * S = G` (`key := h`, MeaningLib PR #42): a row is emitted only when that identity is found, so `Transfer.le` no longer matches every inequality. Transfers 3 (potential) and 5 (`ω`) are frame rules (MeaningLib); 4
(Fock ↔ Haar) and 6 (exact value replacing a bound) are planned on RMTlib#42.
-/

namespace RMT.Transfer

open Finset

/-- **Transfer 1, divisibility**: `Q · S = G ⇒ Q ∣ G`. -/
@[frame_transfer value_bound (key := h)]
theorem dvd {Q S G : ℕ} (h : Q * S = G) : Q ∣ G := Dvd.intro S h

/-- **Transfer 1, valuations at every prime**: `Q · S = G ≠ 0 ⇒ v_p Q + v_p S = v_p G`. -/
@[frame_transfer value_bound (key := h)]
theorem padicValNat_add (p : ℕ) [Fact p.Prime] {Q S G : ℕ} (h : Q * S = G) (hG : G ≠ 0) :
    padicValNat p Q + padicValNat p S = padicValNat p G := by
  have hQ : Q ≠ 0 := fun h0 => hG (by rw [← h, h0, zero_mul])
  have hS : S ≠ 0 := fun h0 => hG (by rw [← h, h0, mul_zero])
  rw [← h, padicValNat.mul hQ hS]

/-- **Transfer 1, size at `∞`**: `Q · S = G ≠ 0 ⇒ Q ≤ G`. -/
@[frame_transfer value_bound (key := h)]
theorem le {Q S G : ℕ} (h : Q * S = G) (hG : G ≠ 0) : Q ≤ G := by
  have hS : S ≠ 0 := fun h0 => hG (by rw [← h, h0, mul_zero])
  calc Q = Q * 1 := (mul_one Q).symm
    _ ≤ Q * S := Nat.mul_le_mul_left Q (Nat.one_le_iff_ne_zero.mpr hS)
    _ = G := h

/-- **Transfer 2, the product formula**: `log Q = Σ_{p ∣ Q} v_p(Q) · log p` for `Q ≠ 0`. -/
@[frame_transfer inf_p]
theorem log_eq_sum {Q : ℕ} (hQ : Q ≠ 0) :
    Real.log Q = ∑ p ∈ Q.primeFactors, (padicValNat p Q : ℝ) * Real.log p := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hQ]
  rw [Finsupp.prod, Nat.cast_prod, Real.log_prod]
  · refine sum_congr rfl fun p hp => ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.factorization_def Q (Nat.prime_of_mem_primeFactors hp)]
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity

/-- **Instance of transfer 1**: the hook-length formula `H(λ) · f^λ = |λ|!`. -/
theorem hook_transfer {N : ℕ} {ν : Fin N → ℕ} (hν : Antitone ν) :
    RMT.hookProd ν * RMT.fSYT (∑ i, ν i) ν = (∑ i, ν i).factorial := by
  rw [mul_comm]
  exact RMT.hook_length_formula ν hν

end RMT.Transfer
