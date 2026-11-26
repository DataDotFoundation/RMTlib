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

namespace RMT

open Finset
open scoped Nat

variable {N : ℕ}

/-- `(n + k)! ≤ n! · M^k` when `n + k ≤ M`. -/
theorem factorial_add_le_mul_pow {n k M : ℕ} (h : n + k ≤ M) : (n + k)! ≤ n ! * M ^ k := by
  have h1 := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
  rw [Nat.add_sub_cancel] at h1
  rw [← h1]
  exact Nat.mul_le_mul_left _ ((Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left h _))

/-- **The one-body part loses at most a polynomial factor** (RMTlib#41, RH-Dual#51):
`H(λ) ≤ ∏_i λ_i! · (λ₀ + N − 1)^{Σ_i (N − 1 − i)}`, with `Σ_i (N − 1 − i) = C(N, 2)`. Together with
`prod_factorial_le_hookProd` this brackets `log H(λ)` between its one-body (row factorial) part and
that part plus `C(N, 2) log (λ₀ + N − 1)`. From Frobenius: `H · Δ = ∏ ℓ_i!`, `Δ ≥ 1`. -/
theorem hookProd_le_prod_factorial_mul_pow (ν : Fin N → ℕ) (hν : Antitone ν) (h0 : 0 < N) :
    hookProd ν ≤ (∏ i, (ν i)!) * (ν ⟨0, h0⟩ + (N - 1)) ^ (∑ i : Fin N, (N - 1 - i)) := by
  have hF := frobenius ν hν
  have hΔ : 1 ≤ ∏ i, ∏ j ∈ Ioi i, (ν i - ν j + (j - i)) := by
    refine Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr ?_)
    intro j hj
    have := mem_Ioi.mp hj
    have : (i : ℕ) < j := this
    omega
  have hle : hookProd ν ≤ ∏ i, (ν i + (N - 1 - i))! :=
    calc hookProd ν ≤ hookProd ν * ∏ i, ∏ j ∈ Ioi i, (ν i - ν j + (j - i)) :=
          Nat.le_mul_of_pos_right _ hΔ
      _ = _ := hF
  refine hle.trans ?_
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_le_prod fun i _ => factorial_add_le_mul_pow ?_
  have := hν (show (⟨0, h0⟩ : Fin N) ≤ i from Fin.mk_le_mk.mpr (Nat.zero_le _))
  have := i.isLt
  omega

end RMT
