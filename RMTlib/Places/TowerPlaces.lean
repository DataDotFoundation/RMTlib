import RMTlib.Places.Tower
import RMTlib.Places.Transfer
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The tower read at every place (RMTlib#79 item 2)

One `RMT.Tower`, one reading per place:
* at `∞`, `log H` of each side (`RMT.Tower.log_hset_above_succ`);
* at a prime `p`, the valuation `v_p(H)` of each side.

They are tied by the **product formula** (`log_hset_eq_sum`):
`log H(L) = Σ_p v_p(H(L)) · log p`, with `H = fac / vd`. And the step law has the **same split at
every prime** (`padicValRat_hset_step`), so a lift has one statement, read at each place:
`v_p` of the new side is `v_p` of the old side plus the translation `Σ (v_p (x+Δ)! − v_p x!)`, plus
the self-energy `v_p ℓ!`, minus the mutual energy `Σ v_p |x + Δ − ℓ|`.

Draining is an inequality at `∞` only: at `p` the valuation of the hole side can go either way.
-/

namespace RMT.StringInsertion

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p` of a finite product of nonzero rationals is the sum of the `v_p`. -/
theorem padicValRat_prod {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℚ}
    (h : ∀ x ∈ s, f x ≠ 0) : padicValRat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValRat p (f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha,
      padicValRat.mul (h a (mem_insert_self a s))
        (prod_ne_zero_iff.mpr fun x hx => h x (mem_insert_of_mem hx)),
      ih fun x hx => h x (mem_insert_of_mem hx)]

/-- `v_p (H L) = v_p (fac L) − v_p (vd L)`. -/
theorem padicValRat_hset (L : Finset ℕ) :
    padicValRat p (hset L) = (padicValNat p (fac L) : ℤ) - padicValNat p (vd L) := by
  unfold hset
  rw [padicValRat.div (by exact_mod_cast (fac_pos L).ne') (by exact_mod_cast (vd_pos L).ne'),
    padicValRat.of_nat, padicValRat.of_nat]

/-- **The step law at a prime `p`**: the same split as at `∞` (`log_hset_step`). -/
theorem padicValRat_hset_step {L : Finset ℕ} {Δ ℓ : ℕ} (hℓ : ℓ ∉ shift L Δ) :
    padicValRat p (hset (insert ℓ (shift L Δ))) =
      padicValRat p (hset L) +
      (∑ x ∈ L, ((padicValNat p (x + Δ).factorial : ℤ) - padicValNat p x.factorial)) +
      padicValNat p ℓ.factorial -
      ∑ x ∈ L, (padicValNat p (Nat.dist (x + Δ) ℓ) : ℤ) := by
  have hd : ∀ x ∈ L, (Nat.dist (x + Δ) ℓ : ℚ) ≠ 0 := by
    intro x hx h
    have h0 : Nat.dist (x + Δ) ℓ = 0 := by exact_mod_cast h
    exact hℓ (Nat.eq_of_dist_eq_zero h0 ▸ mem_shift.mpr ⟨x, hx, rfl⟩)
  have hT : ∀ x ∈ L, (((x + Δ).factorial : ℚ) / x.factorial) ≠ 0 := fun x _ => by
    have := Nat.factorial_pos x; have := Nat.factorial_pos (x + Δ); positivity
  have hH : hset L ≠ 0 := (hset_pos L).ne'
  have hS : (ℓ.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos ℓ).ne'
  rw [hset_step hℓ,
    padicValRat.div (mul_ne_zero (mul_ne_zero hH (prod_ne_zero_iff.mpr hT)) hS)
      (prod_ne_zero_iff.mpr hd),
    padicValRat.mul (mul_ne_zero hH (prod_ne_zero_iff.mpr hT)) hS,
    padicValRat.mul hH (prod_ne_zero_iff.mpr hT), padicValRat_prod hT, padicValRat_prod hd,
    padicValRat.of_nat]
  congr 2
  · congr 1
    refine sum_congr rfl fun x _ => ?_
    rw [padicValRat.div (by exact_mod_cast (Nat.factorial_pos _).ne')
      (by exact_mod_cast (Nat.factorial_pos _).ne'), padicValRat.of_nat, padicValRat.of_nat]
  · funext x
    exact padicValRat.of_nat

omit hp in
/-- Extend `log_eq_sum` to a larger set of primes: the extra primes have valuation zero. -/
theorem log_eq_sum_of_subset {Q : ℕ} (hQ : Q ≠ 0) {S : Finset ℕ} (hS : Q.primeFactors ⊆ S)
    (hprime : ∀ q ∈ S, q.Prime) :
    Real.log Q = ∑ q ∈ S, (padicValNat q Q : ℝ) * Real.log q := by
  rw [RMT.Transfer.log_eq_sum hQ]
  refine sum_subset hS fun q hqS hq => ?_
  have hqp := hprime q hqS
  have : ¬ q ∣ Q := fun hdvd => hq (Nat.mem_primeFactors.mpr ⟨hqp, hdvd, hQ⟩)
  rw [padicValNat.eq_zero_of_not_dvd this]
  simp

omit hp in
/-- **The product formula for `H`**: `log H(L) = Σ_p v_p(H(L)) · log p`, over the primes of
`fac L · vd L`. -/
theorem log_hset_eq_sum (L : Finset ℕ) :
    Real.log (hset L) =
      ∑ q ∈ (fac L * vd L).primeFactors, (padicValRat q (hset L) : ℝ) * Real.log q := by
  have hf := (fac_pos L).ne'
  have hv := (vd_pos L).ne'
  have hprime : ∀ q ∈ (fac L * vd L).primeFactors, q.Prime := fun q hq =>
    Nat.prime_of_mem_primeFactors hq
  have h1 : (fac L).primeFactors ⊆ (fac L * vd L).primeFactors := by
    rw [Nat.primeFactors_mul hf hv]; exact subset_union_left
  have h2 : (vd L).primeFactors ⊆ (fac L * vd L).primeFactors := by
    rw [Nat.primeFactors_mul hf hv]; exact subset_union_right
  have hcast : ((hset L : ℚ) : ℝ) = (fac L : ℝ) / vd L := by
    unfold hset; push_cast; rfl
  rw [hcast, Real.log_div (by exact_mod_cast hf) (by exact_mod_cast hv),
    log_eq_sum_of_subset hf h1 hprime, log_eq_sum_of_subset hv h2 hprime, ← sum_sub_distrib]
  refine sum_congr rfl fun q hq => ?_
  have : Fact q.Prime := ⟨hprime q hq⟩
  rw [padicValRat_hset]
  simp only [Int.cast_sub, Int.cast_natCast]
  ring

end RMT.StringInsertion

namespace RMT.Tower

open Finset RMT.StringInsertion

variable (T : RMT.Tower) {p : ℕ} [Fact p.Prime]

/-- **The tower's step at a prime `p`**: on the particle side, `v_p` changes by the translation,
the self-energy and the mutual energy, the same split as at `∞` (`log_hset_above_succ`). -/
theorem padicValRat_above_succ {i : ℕ} {z : ℤ} (h : T.StepOK i z) :
    padicValRat p (hset (T.cut (i + 1)).1) =
      padicValRat p (hset (T.cut i).1) +
      (∑ x ∈ (T.cut i).1, ((padicValNat p (x + (T.gap i).toNat).factorial : ℤ) -
        padicValNat p x.factorial)) +
      padicValNat p (z + T.gap i - T.c).toNat.factorial -
      ∑ x ∈ (T.cut i).1, (padicValNat p (Nat.dist (x + (T.gap i).toNat) (z + T.gap i - T.c).toNat) : ℤ) := by
  rw [T.cut_succ_fst h]
  exact padicValRat_hset_step (crossing_not_mem_shift_above h.hc h.hd h.one)

/-- **The factor at `∞` from its readings at the primes**: `log (H(a⁺_i) H(a⁻_i))` is the sum over
primes of the two valuations times `log p`. -/
theorem log_factorInf_eq_sum (i : ℕ) :
    Real.log (T.factorInf i) =
      (∑ q ∈ (fac (T.cut i).1 * vd (T.cut i).1).primeFactors,
        (padicValRat q (hset (T.cut i).1) : ℝ) * Real.log q) +
      ∑ q ∈ (fac (T.cut i).2 * vd (T.cut i).2).primeFactors,
        (padicValRat q (hset (T.cut i).2) : ℝ) * Real.log q := by
  unfold factorInf
  push_cast
  rw [Real.log_mul (by exact_mod_cast (hset_pos _).ne') (by exact_mod_cast (hset_pos _).ne'),
    log_hset_eq_sum, log_hset_eq_sum]

end RMT.Tower
