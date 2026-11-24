import Mathlib.RingTheory.MvPowerSeries.PiTopology

/-!
# Valued sets in `MvPowerSeries`

Following Mitchell Lee's proposal on the Lean Zulip ("(Unlabeled) enumerative combinatorics",
March 2024), a *valued set* is a type `A` with a weight `w : A → (ι →₀ ℕ)`; its total weight is
`∑' a, X ^ (w a)` in `MvPowerSeries ι R` with the product topology. When every fibre of `w` is
finite the family is summable, and the coefficient of `X ^ d` is the number of elements of
weight `d`. An equivalence of types that preserves weights is then an identity of power series in
all degrees at once.

## Main results

* `FiniteFibres w`: every fibre of `w` is finite.
* `summable_mono`: finite fibres give a summable family of monomials.
* `coeff_tsum_mono`: the coefficient of `X ^ d` in the total weight is the size of the fibre.
* `FiniteFibres.comp_injective`: finite fibres pass to subtypes and other injections.
* `tsum_mono_mul`: the product of two total weights is the total weight of the product, with
  the sum of the weights.
* `tsum_mono_pi`: the total weight of `K → ℕ`, weighted by `Σ_k A k • v k`, is the product over
  `k` of the geometric series `Σ' t, X ^ (t • v k)` (for `K` finite and every `v k ≠ 0`).
* `one_sub_mul_tsum_mono_smul`: `(1 − X ^ v) * Σ' t, X ^ (t • v) = 1`.
-/

open scoped MvPowerSeries.WithPiTopology
open MvPowerSeries

namespace RMT.Symmetric

variable {ι R A B : Type*} [CommSemiring R] [TopologicalSpace R]

/-- The monomial `X ^ d` with coefficient `1`. -/
noncomputable abbrev mono (d : ι →₀ ℕ) : MvPowerSeries ι R := monomial d 1

/-- Every fibre of the weight `w` is finite. -/
def FiniteFibres (w : A → ι →₀ ℕ) : Prop := ∀ d, {a | w a = d}.Finite

omit [TopologicalSpace R] in
theorem support_coeff_mono_subset (w : A → ι →₀ ℕ) (d : ι →₀ ℕ) :
    Function.support (fun a => coeff d (mono (w a) : MvPowerSeries ι R)) ⊆ {a | w a = d} := by
  classical
  intro a ha
  simp only [Function.mem_support, coeff_monomial] at ha
  by_contra h
  exact ha (if_neg fun e => h e.symm)

/-- **Finite fibres give a summable family of monomials.** -/
theorem summable_mono {w : A → ι →₀ ℕ} (hw : FiniteFibres w) :
    Summable (fun a => (mono (w a) : MvPowerSeries ι R)) := by
  rw [WithPiTopology.summable_iff_summable_coeff]
  intro d
  exact summable_of_hasFiniteSupport ((hw d).subset (support_coeff_mono_subset w d))

/-- **The coefficients of a total weight count the fibres.** -/
theorem coeff_tsum_mono [T2Space R] {w : A → ι →₀ ℕ} (hw : FiniteFibres w) (d : ι →₀ ℕ) :
    coeff d (∑' a, (mono (w a) : MvPowerSeries ι R)) = ((hw d).toFinset.card : R) := by
  classical
  have h := ((summable_mono (R := R) hw).hasSum)
  rw [WithPiTopology.hasSum_iff_hasSum_coeff] at h
  refine ((h d).unique ?_)
  have : (fun a => coeff d (mono (w a) : MvPowerSeries ι R))
      = fun a => if a ∈ (hw d).toFinset then (1 : R) else 0 := by
    funext a
    simp only [coeff_monomial, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    by_cases h : w a = d
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this]
  have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional A)
    (f := fun a => if a ∈ (hw d).toFinset then (1 : R) else 0)
    (s := (hw d).toFinset) (fun a ha => if_neg ha)
  rwa [Finset.sum_ite_of_true (fun _ h => h), Finset.sum_const, nsmul_one] at this

/-- Finite fibres pass along injections. -/
theorem FiniteFibres.comp_injective {w : A → ι →₀ ℕ} (hw : FiniteFibres w) {f : B → A}
    (hf : Function.Injective f) : FiniteFibres (w ∘ f) :=
  fun d => (hw d).preimage hf.injOn

/-- Finitely many elements have weight at most `d`. -/
theorem FiniteFibres.finite_le {w : A → ι →₀ ℕ} (hw : FiniteFibres w) (d : ι →₀ ℕ) :
    {a | w a ≤ d}.Finite := by
  classical
  have : {a | w a ≤ d} = ⋃ e ∈ Set.Iic d, {a | w a = e} := by
    ext a
    simp
  rw [this]
  exact (Set.finite_Iic d).biUnion (fun e _ => hw e)

/-- The sum of two weights with finite fibres has finite fibres. -/
theorem FiniteFibres.add {w : A → ι →₀ ℕ} {w' : B → ι →₀ ℕ} (hw : FiniteFibres w)
    (hw' : FiniteFibres w') : FiniteFibres (fun p : A × B => w p.1 + w' p.2) := by
  intro d
  refine ((hw.finite_le d).prod (hw'.finite_le d)).subset ?_
  rintro ⟨a, b⟩ h
  have h' : w a + w' b = d := h
  exact ⟨show w a ≤ d by rw [← h']; exact le_self_add,
    show w' b ≤ d by rw [← h']; exact le_add_self⟩

/-- A nonzero weight `v` gives the multiples `t ↦ t • v` finite fibres. -/
theorem finiteFibres_smul {v : ι →₀ ℕ} (hv : v ≠ 0) : FiniteFibres (fun t : ℕ => t • v) := by
  intro d
  refine Set.Subsingleton.finite ?_
  intro s hs t ht
  have h : s • v = t • v := (hs : s • v = d).trans (ht : t • v = d).symm
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hv
  have := congrArg (fun f => f i) h
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at this hi
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) this

section Products

variable [IsTopologicalSemiring R] [T3Space R]

/-- **Products of valued sets.** -/
theorem tsum_mono_mul {w : A → ι →₀ ℕ} {w' : B → ι →₀ ℕ} (hw : FiniteFibres w)
    (hw' : FiniteFibres w') :
    (∑' a, (mono (w a) : MvPowerSeries ι R)) * (∑' b, (mono (w' b) : MvPowerSeries ι R))
      = ∑' p : A × B, (mono (w p.1 + w' p.2) : MvPowerSeries ι R) := by
  have : T3Space (MvPowerSeries ι R) := inferInstanceAs (T3Space ((ι →₀ ℕ) → R))
  have hmul : ∀ p : A × B, (mono (w p.1) : MvPowerSeries ι R) * mono (w' p.2)
      = mono (w p.1 + w' p.2) := fun p => by rw [monomial_mul_monomial, one_mul]
  have h1 : Summable (fun a => (mono (w a) : MvPowerSeries ι R)) := summable_mono hw
  have h2 : Summable (fun b => (mono (w' b) : MvPowerSeries ι R)) := summable_mono hw'
  have h3 : Summable (fun p : A × B => (mono (w p.1) : MvPowerSeries ι R) * mono (w' p.2)) := by
    simp only [hmul]
    exact summable_mono (hw.add hw')
  rw [h1.tsum_mul_tsum h2 h3]
  simp only [hmul]

/-- **Finite products of geometric series.** For a finite type `K` and nonzero weights `v k`,
the functions `A : K → ℕ` weighted by `Σ_k A k • v k` have finite fibres, and their total weight
is `∏_k Σ' t, X ^ (t • v k)`. -/
theorem tsum_mono_pi_fin : ∀ (r : ℕ) (v : Fin r → ι →₀ ℕ), (∀ k, v k ≠ 0) →
    FiniteFibres (fun A : Fin r → ℕ => ∑ k, A k • v k) ∧
    ∑' A : Fin r → ℕ, (mono (∑ k, A k • v k) : MvPowerSeries ι R)
      = ∏ k, ∑' t : ℕ, (mono (t • v k) : MvPowerSeries ι R)
  | 0, v, _ => by
    refine ⟨fun d => Set.toFinite _, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, tsum_fintype]
    simp [mono, monomial_zero_eq_C_apply]
  | r + 1, v, hv => by
    obtain ⟨ih1, ih2⟩ := tsum_mono_pi_fin r (fun k => v k.succ) (fun k => hv k.succ)
    let e := Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)
    have hw : ∀ p : ℕ × (Fin r → ℕ), (∑ k, (e p) k • v k)
        = p.1 • v 0 + ∑ k : Fin r, p.2 k • v k.succ := by
      intro p
      rw [Fin.sum_univ_succ]
      rfl
    have hf : FiniteFibres (fun p : ℕ × (Fin r → ℕ) => p.1 • v 0 + ∑ k : Fin r, p.2 k • v k.succ) :=
      (finiteFibres_smul (hv 0)).add ih1
    have hf' : FiniteFibres (fun A : Fin (r + 1) → ℕ => ∑ k, A k • v k) := by
      have := hf.comp_injective e.symm.injective
      convert this using 1
      funext A
      simp only [Function.comp_apply]
      rw [← hw, Equiv.apply_symm_apply]
    refine ⟨hf', ?_⟩
    rw [← e.tsum_eq, Fin.prod_univ_succ, ← ih2, tsum_mono_mul (finiteFibres_smul (hv 0)) ih1]
    simp only [hw]

/-- **Finite products of geometric series**, for any finite index type. -/
theorem tsum_mono_pi {K : Type*} [Fintype K] (v : K → ι →₀ ℕ) (hv : ∀ k, v k ≠ 0) :
    FiniteFibres (fun A : K → ℕ => ∑ k, A k • v k) ∧
    ∑' A : K → ℕ, (mono (∑ k, A k • v k) : MvPowerSeries ι R)
      = ∏ k, ∑' t : ℕ, (mono (t • v k) : MvPowerSeries ι R) := by
  let e := Fintype.equivFin K
  obtain ⟨h1, h2⟩ := tsum_mono_pi_fin (R := R) (Fintype.card K) (fun i => v (e.symm i))
    (fun i => hv _)
  let E : (K → ℕ) ≃ (Fin (Fintype.card K) → ℕ) := e.arrowCongr (Equiv.refl ℕ)
  have hw : ∀ A : K → ℕ, ∑ k, A k • v k = ∑ i, (E A) i • v (e.symm i) := by
    intro A
    rw [← e.symm.sum_comp]
    rfl
  refine ⟨?_, ?_⟩
  · have := h1.comp_injective E.injective
    convert this using 1
    funext A
    exact hw A
  · calc ∑' A : K → ℕ, (mono (∑ k, A k • v k) : MvPowerSeries ι R)
        = ∑' A : K → ℕ, (mono (∑ i, (E A) i • v (e.symm i)) : MvPowerSeries ι R) := by
          simp only [hw]
      _ = ∏ i, ∑' t : ℕ, (mono (t • v (e.symm i)) : MvPowerSeries ι R) :=
          (E.tsum_eq (fun B => (mono (∑ i, B i • v (e.symm i)) : MvPowerSeries ι R))).trans h2
      _ = ∏ k, ∑' t : ℕ, (mono (t • v k) : MvPowerSeries ι R) :=
          e.symm.prod_comp (fun k => ∑' t : ℕ, (mono (t • v k) : MvPowerSeries ι R))

end Products

section Geometric

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/-- **The geometric series of a monomial**: `(1 − X ^ v) * Σ' t, X ^ (t • v) = 1` for `v ≠ 0`. -/
theorem one_sub_mul_tsum_mono_smul {v : ι →₀ ℕ} (hv : v ≠ 0) :
    (1 - (mono v : MvPowerSeries ι R)) * ∑' t : ℕ, (mono (t • v) : MvPowerSeries ι R) = 1 := by
  classical
  have h : constantCoeff (mono v : MvPowerSeries ι R) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg (Ne.symm hv)]
  have := WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero h
  simpa only [monomial_pow, one_pow] using this

end Geometric

end RMT.Symmetric
