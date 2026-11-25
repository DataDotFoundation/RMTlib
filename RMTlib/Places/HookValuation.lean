import RMTlib.Tableaux.HookLengthFormula
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import MeaningLib.Frame.Pattern

/-!
# Hook products at every place

RMTlib#41 (from RH-Dual's `bridge/links/homogeneous-slack.md`). A bound that holds at `∞` only
(Alpöge's node-4 `(n!)^{2R}(R!)^n`, which fails at some prime for 47 of 251 shapes) should be
replaced by an exact statement that holds at every place. For the hook product `H(λ)`:

* `hookProd_dvd_factorial`: **`H(λ) ∣ |λ|!`**, from the hook-length formula `f^λ · H(λ) = |λ|!`.
  So the slack `f^λ` is homogeneous: the same statement at `∞` and at every prime.
* `padicValNat_hookProd_add_fSYT`: at every prime, `v_p H(λ) + v_p f^λ = v_p |λ|!`.
* `padicValNat_hookProd`: at every prime, `v_p H(λ) = Σ_{□ ∈ λ} v_p h(□)`. Together with Legendre's
  formula for `v_p |λ|!` (Mathlib `padicValNat_factorial`), `v_p f^λ` is a box statistic.

All three are `@[frame_pattern]`. Next (RMTlib#41): `v_p h = #{j ≥ 1 : p^j ∣ h}` and Littlewood's
count `#{□ : p ∣ h(□)} = |p-quotient|`, then content products, then heights.
-/

open Finset
open scoped Nat

namespace RMT

variable {N : ℕ}

/-- The valuation of a product of nonzero naturals is the sum of the valuations. -/
theorem padicValNat_finset_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValNat.mul (hf a (mem_insert_self a s))
      (prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- `H(λ) ≠ 0`. -/
theorem hookProd_ne_zero {ν : Fin N → ℕ} (hν : Antitone ν) : hookProd ν ≠ 0 := by
  intro h
  have := hook_length_formula ν hν
  rw [h, mul_zero] at this
  exact (Nat.factorial_ne_zero _) this.symm

/-- **Homogeneous bound**: `H(λ) ∣ |λ|!`, the same statement at every place. -/
@[frame_pattern]
theorem hookProd_dvd_factorial {ν : Fin N → ℕ} (hν : Antitone ν) :
    hookProd ν ∣ (∑ i, ν i)! :=
  Dvd.intro_left _ (hook_length_formula ν hν)

/-- **At every prime**: `v_p H(λ) + v_p f^λ = v_p |λ|!`. -/
@[frame_pattern]
theorem padicValNat_hookProd_add_fSYT (p : ℕ) [Fact p.Prime] {ν : Fin N → ℕ} (hν : Antitone ν) :
    padicValNat p (hookProd ν) + padicValNat p (fSYT (∑ i, ν i) ν) =
      padicValNat p (∑ i, ν i)! := by
  have hH := hookProd_ne_zero hν
  have hf : fSYT (∑ i, ν i) ν ≠ 0 := by
    intro h
    have := hook_length_formula ν hν
    rw [h, zero_mul] at this
    exact (Nat.factorial_ne_zero _) this.symm
  rw [← hook_length_formula ν hν, padicValNat.mul hf hH, add_comm]

/-- **At every prime, box by box**: `v_p H(λ) = Σ_{□ ∈ λ} v_p h(□)`. -/
@[frame_pattern]
theorem padicValNat_hookProd (p : ℕ) [Fact p.Prime] {ν : Fin N → ℕ} (hν : Antitone ν) :
    padicValNat p (hookProd ν) =
      ∑ i, ∑ c ∈ range (ν i), padicValNat p (hook ν i c) := by
  have hH := hookProd_ne_zero hν
  unfold hookProd at hH ⊢
  have hrow : ∀ i ∈ (univ : Finset (Fin N)), ∏ c ∈ range (ν i), hook ν i c ≠ 0 :=
    fun i _ => (prod_ne_zero_iff.mp hH) i (mem_univ i)
  rw [padicValNat_finset_prod p _ _ hrow]
  refine sum_congr rfl fun i hi => ?_
  exact padicValNat_finset_prod p _ _ fun c hc => (prod_ne_zero_iff.mp (hrow i hi)) c hc

end RMT
