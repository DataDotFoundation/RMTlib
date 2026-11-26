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
  simp only [Nat.padicValNat_def]
  rw [← h, Nat.multiplicity_mul hQ hS]

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
    rw [Nat.cast_pow, Real.log_pow, Nat.factorization_def Q (Nat.prime_of_mem_primeFactors hp),
      Nat.padicValNat_def]
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity

/-- Over any set of primes, `Σ log ℓ · v_ℓ(Q) ≤ log Q` for `Q ≠ 0` (the product formula, truncated). -/
@[frame_transfer inf_p]
theorem sum_log_mul_padicValNat_le {Q : ℕ} (hQ : Q ≠ 0) (Ls : Finset Nat.Primes) :
    ∑ ℓ ∈ Ls, Real.log (ℓ : ℕ) * (padicValNat ℓ Q : ℝ) ≤ Real.log Q := by
  classical
  rw [log_eq_sum hQ]
  let e : Nat.Primes ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : ∑ ℓ ∈ Ls, Real.log (ℓ : ℕ) * (padicValNat ℓ Q : ℝ) =
      ∑ x ∈ Ls.map e, Real.log x * (padicValNat x Q : ℝ) :=
    (Finset.sum_map Ls e (fun x : ℕ => Real.log x * (padicValNat x Q : ℝ))).symm
  rw [hmap, ← sum_filter_add_sum_filter_not _ (· ∈ Q.primeFactors)]
  have hzero : ∑ x ∈ (Ls.map e).filter (· ∉ Q.primeFactors),
      Real.log x * (padicValNat x Q : ℝ) = 0 := by
    refine sum_eq_zero fun x hx => ?_
    obtain ⟨hxL, hxQ⟩ := mem_filter.mp hx
    obtain ⟨ℓ, -, rfl⟩ := mem_map.mp hxL
    have : ¬ (ℓ : ℕ) ∣ Q := fun hd => hxQ (Nat.mem_primeFactors.mpr ⟨ℓ.2, hd, hQ⟩)
    have h0 : padicValNat (e ℓ) Q = 0 := by
      rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd this
    rw [h0, Nat.cast_zero, mul_zero]
  rw [hzero, add_zero]
  calc _ ≤ ∑ p ∈ Q.primeFactors, Real.log p * (padicValNat p Q : ℝ) := by
        refine sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.mp hx).2) ?_
        intro p hp _
        have := (Nat.prime_of_mem_primeFactors hp).one_lt
        exact mul_nonneg (Real.log_nonneg (by exact_mod_cast this.le)) (Nat.cast_nonneg _)
    _ = _ := sum_congr rfl fun p _ => mul_comm _ _

/-- **The truncated product formula over a `Finset ℕ` of primes, bounded at any `b ≥ a`**: the exact
shape of the condensed edition's `New.Selmer.sum_padicValNat_mul_log_le` (RMTlib#140), from
`sum_log_mul_padicValNat_le` by three adapters (a `Finset ℕ` with a primality hypothesis for
`Nat.Primes`, the product order, and `log a ≤ log b`), and the case `a = 0`. -/
theorem sum_padicValNat_mul_log_le (T : Finset ℕ) (hT : ∀ l ∈ T, l.Prime) {a b : ℕ}
    (hab : a ≤ b) : ∑ l ∈ T, (padicValNat l a : ℝ) * Real.log l ≤ Real.log b := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h0 : ∀ l ∈ T, (padicValNat l 0 : ℝ) * Real.log l = 0 := fun l _ => by
      simp [padicValNat]
    rw [Finset.sum_eq_zero h0]
    exact Real.log_natCast_nonneg b
  · have h := sum_log_mul_padicValNat_le ha.ne' (T.subtype Nat.Prime)
    calc ∑ l ∈ T, (padicValNat l a : ℝ) * Real.log l
        = ∑ l ∈ T, Real.log l * (padicValNat l a : ℝ) := Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = ∑ ℓ ∈ T.subtype Nat.Prime, Real.log ((ℓ : ℕ)) * (padicValNat ℓ a : ℝ) :=
          (Finset.sum_subtype_of_mem (fun l : ℕ => Real.log l * (padicValNat l a : ℝ)) hT).symm
      _ ≤ Real.log a := h
      _ ≤ Real.log b := Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)

/-- **Two auxiliary primes cover every prime** (RH-Dual on MeaningLib#51; the content of the proof's
`corGK` without Ш). If `a_ℓ ≤ c · v_ℓ(n)` for every prime `ℓ ≠ p` and `a_ℓ ≤ c · v_ℓ(n′)` for every
prime `ℓ ≠ p′`, with `p ≠ p′`, then over any set of primes
`Σ log ℓ · a_ℓ ≤ c · (log |n| + log |n′|)`. The choice of `p`, `p′` (size or bad-set conditions) stays a
hypothesis of the pattern, not a transfer. -/
@[frame_transfer inf_p]
theorem sum_log_le_of_two_aux {a : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {p p' : ℕ} (hne : p ≠ p')
    {n n' : ℤ} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → a ℓ ≤ c * padicValInt ℓ n)
    (h' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p' → a ℓ ≤ c * padicValInt ℓ n')
    (Ls : Finset Nat.Primes) :
    ∑ ℓ ∈ Ls, Real.log (ℓ : ℕ) * a ℓ ≤ c * (Real.log |(n : ℝ)| + Real.log |(n' : ℝ)|) := by
  have hcover : ∀ ℓ ∈ Ls, Real.log (ℓ : ℕ) * a ℓ ≤
      c * (Real.log (ℓ : ℕ) * padicValNat ℓ n.natAbs + Real.log (ℓ : ℕ) * padicValNat ℓ n'.natAbs) := by
    intro ℓ _
    have hlog : 0 ≤ Real.log (ℓ : ℕ) := Real.log_nonneg (by exact_mod_cast ℓ.2.one_lt.le)
    have hv : 0 ≤ (padicValNat ℓ n.natAbs : ℝ) := Nat.cast_nonneg _
    have hv' : 0 ≤ (padicValNat ℓ n'.natAbs : ℝ) := Nat.cast_nonneg _
    have hbound : a ℓ ≤ c * padicValNat ℓ n.natAbs + c * padicValNat ℓ n'.natAbs := by
      by_cases hp : (ℓ : ℕ) = p
      · have := h' ℓ ℓ.2 (hp ▸ hne)
        simp only [padicValInt, ← Nat.padicValNat_def] at this
        nlinarith [mul_nonneg hc hv]
      · have := h ℓ ℓ.2 hp
        simp only [padicValInt, ← Nat.padicValNat_def] at this
        nlinarith [mul_nonneg hc hv']
    nlinarith [mul_le_mul_of_nonneg_left hbound hlog]
  calc ∑ ℓ ∈ Ls, Real.log (ℓ : ℕ) * a ℓ
      ≤ ∑ ℓ ∈ Ls, c * (Real.log (ℓ : ℕ) * padicValNat ℓ n.natAbs +
          Real.log (ℓ : ℕ) * padicValNat ℓ n'.natAbs) := sum_le_sum hcover
    _ = c * (∑ ℓ ∈ Ls, Real.log (ℓ : ℕ) * padicValNat ℓ n.natAbs +
          ∑ ℓ ∈ Ls, Real.log (ℓ : ℕ) * padicValNat ℓ n'.natAbs) := by
        rw [← mul_sum, sum_add_distrib]
    _ ≤ c * (Real.log n.natAbs + Real.log n'.natAbs) := by
        gcongr
        · exact sum_log_mul_padicValNat_le (Int.natAbs_ne_zero.mpr hn) Ls
        · exact sum_log_mul_padicValNat_le (Int.natAbs_ne_zero.mpr hn') Ls
    _ = c * (Real.log |(n : ℝ)| + Real.log |(n' : ℝ)|) := by
        simp [Nat.cast_natAbs]

/-- **Folding `padicValInt`** (MeaningLib#68 R3): `v_p` of an integer is `v_p` of its absolute value. -/
theorem padicValInt_eq_padicValNat_natAbs (p : ℕ) (n : ℤ) :
    padicValInt p n = padicValNat p n.natAbs := by
  rw [padicValInt, Nat.padicValNat_def]

/-- **The truncated product formula over `ℤ`** (MeaningLib#68 R3), in the form the proof states it:
over any set of primes, `Σ log ℓ · v_ℓ(n) ≤ log |n|` for `n ≠ 0`. -/
@[frame_transfer inf_p]
theorem sum_log_mul_padicValInt_le {n : ℤ} (hn : n ≠ 0) (Ls : Finset Nat.Primes) :
    ∑ ℓ ∈ Ls, Real.log (ℓ : ℕ) * (padicValInt ℓ n : ℝ) ≤ Real.log |(n : ℝ)| := by
  have h := sum_log_mul_padicValNat_le (Int.natAbs_ne_zero.mpr hn) Ls
  simpa [padicValInt_eq_padicValNat_natAbs, Nat.cast_natAbs] using h

/-- **Instance of transfer 1**: the hook-length formula `H(λ) · f^λ = |λ|!`. -/
theorem hook_transfer {N : ℕ} {ν : Fin N → ℕ} (hν : Antitone ν) :
    RMT.hookProd ν * RMT.fSYT (∑ i, ν i) ν = (∑ i, ν i).factorial := by
  rw [mul_comm]
  exact RMT.hook_length_formula ν hν

end RMT.Transfer
