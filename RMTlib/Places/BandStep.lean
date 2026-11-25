import RMTlib.Places.StringInsertion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# One lift is one step: `Δ log H = T + S + V` (RMTlib#72, #70)

RH-Dual's picture (`slack-growth.md` §band): at each place the HC parameter is one Maya diagram,
cut at a Fermi gap; `a⁺` is the particle side, `a⁻` the hole side. A lift slides the diagram by
`Δ`, and exactly one point crosses the gap. On the particle side that is: translate the old
charges by `Δ`, then insert the new charge `ℓ`. With `H(L) = fac L / vd L` (Frobenius, in Maya
coordinates; `RMT.StringInsertion`):

* `vd_shift`: a translation does not change the Vandermonde;
* `fac_shift`: it changes `fac` by `∏ (x + Δ)!` against `∏ x!`;
* `hset_insert`: inserting `ℓ` multiplies `H` by `ℓ! / ∏ |x − ℓ|`;
* `hset_step` and `log_hset_step`: **the step law**
  `log H(insert ℓ (L + Δ)) − log H(L) = T + S + V`, with
  `T = Σ_{x ∈ L} log ((x + Δ)! / x!)` (translation),
  `S = log ℓ!` (the new charge's self-energy),
  `V = −Σ_{x ∈ L} log |x + Δ − ℓ|` (Vandermonde, the mutual energy).

This is RH-Dual's computed law (exceptionless on 1.29 M parameter sets) as an identity, for every
finite Maya set and every crossing point not already occupied. The hole side is the same lemmas
read backwards (`hset_insert` for the removal of the hole that crossed, `vd_shift`, `fac_shift`
for the translation down). Draining (`H` of the hole side never increases) is an inequality and is
not proved here.
-/

namespace RMT.StringInsertion

open Finset

/-- Translate a Maya set by `Δ`. -/
def shift (L : Finset ℕ) (Δ : ℕ) : Finset ℕ := L.map (addRightEmbedding Δ)

@[simp] theorem shift_empty (Δ : ℕ) : shift ∅ Δ = ∅ := rfl

theorem shift_insert (a : ℕ) (L : Finset ℕ) (Δ : ℕ) :
    shift (insert a L) Δ = insert (a + Δ) (shift L Δ) := by
  simp [shift, map_insert]

theorem mem_shift {L : Finset ℕ} {Δ y : ℕ} : y ∈ shift L Δ ↔ ∃ x ∈ L, x + Δ = y := by
  simp [shift]

/-- **A translation does not change the Vandermonde.** -/
theorem vd_shift (L : Finset ℕ) (Δ : ℕ) : vd (shift L Δ) = vd L := by
  induction L using Finset.induction_on with
  | empty => rfl
  | insert a L haL ih =>
    have ha' : a + Δ ∉ shift L Δ := by
      rw [mem_shift]; rintro ⟨x, hx, h⟩; exact haL ((by omega : x = a) ▸ hx)
    rw [shift_insert, vd_insert ha', vd_insert haL, ih]
    congr 1
    simp only [shift, prod_map, addRightEmbedding_apply]
    exact prod_congr rfl fun x _ => Nat.dist_add_add_right x Δ a

/-- The translation changes `fac` factor by factor. -/
theorem fac_shift (L : Finset ℕ) (Δ : ℕ) : fac (shift L Δ) = ∏ x ∈ L, (x + Δ).factorial := by
  simp [fac, shift, prod_map]

/-- The hook product in Maya coordinates, `H(L) = fac L / vd L`. -/
noncomputable def hset (L : Finset ℕ) : ℚ := (fac L : ℚ) / vd L

theorem vd_pos (L : Finset ℕ) : 0 < vd L := by
  unfold vd
  refine prod_pos fun x _ => prod_pos fun y hy => ?_
  have := (mem_filter.mp hy).2
  omega

theorem fac_pos (L : Finset ℕ) : 0 < fac L :=
  prod_pos fun x _ => Nat.factorial_pos x

theorem hset_pos (L : Finset ℕ) : 0 < hset L := by
  unfold hset
  have := vd_pos L; have := fac_pos L
  positivity

/-- **Inserting one charge** multiplies `H` by its self-energy over its mutual energy. -/
theorem hset_insert {L : Finset ℕ} {a : ℕ} (ha : a ∉ L) :
    hset (insert a L) = hset L * a.factorial / ∏ x ∈ L, (Nat.dist x a : ℚ) := by
  unfold hset fac
  rw [vd_insert ha, prod_insert ha]
  push_cast
  have hv : (vd L : ℚ) ≠ 0 := by exact_mod_cast (vd_pos L).ne'
  have hd : (∏ x ∈ L, (Nat.dist x a : ℚ)) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro x hx
    have : x ≠ a := fun h => ha (h ▸ hx)
    have : Nat.dist x a ≠ 0 := fun h => this (Nat.eq_of_dist_eq_zero h)
    exact_mod_cast this
  field_simp

/-- **A translation** multiplies `H` by `∏ (x + Δ)! / x!`. -/
theorem hset_shift (L : Finset ℕ) (Δ : ℕ) :
    hset (shift L Δ) = hset L * ∏ x ∈ L, ((x + Δ).factorial : ℚ) / x.factorial := by
  unfold hset
  rw [vd_shift, fac_shift, fac]
  push_cast
  rw [prod_div_distrib]
  have hf : (∏ x ∈ L, (x.factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun x _ => by exact_mod_cast (Nat.factorial_pos x).ne'
  field_simp

/-- **One lift, multiplicatively**: translate by `Δ`, then insert the crossing charge `ℓ`. -/
theorem hset_step {L : Finset ℕ} {Δ ℓ : ℕ} (hℓ : ℓ ∉ shift L Δ) :
    hset (insert ℓ (shift L Δ)) =
      hset L * (∏ x ∈ L, ((x + Δ).factorial : ℚ) / x.factorial) * ℓ.factorial /
        ∏ x ∈ L, (Nat.dist (x + Δ) ℓ : ℚ) := by
  rw [hset_insert hℓ, hset_shift]
  simp [shift, prod_map]

/-- **The step law `Δ log H = T + S + V`**, as an identity: translation `T`, self-energy `S`,
Vandermonde `V ≤ 0`. -/
theorem log_hset_step {L : Finset ℕ} {Δ ℓ : ℕ} (hℓ : ℓ ∉ shift L Δ) :
    Real.log (hset (insert ℓ (shift L Δ))) - Real.log (hset L) =
      (∑ x ∈ L, Real.log (((x + Δ).factorial : ℝ) / x.factorial)) +
      Real.log ℓ.factorial -
      ∑ x ∈ L, Real.log (Nat.dist (x + Δ) ℓ : ℝ) := by
  have hd : ∀ x ∈ L, (Nat.dist (x + Δ) ℓ : ℝ) ≠ 0 := by
    intro x hx h
    have h0 : Nat.dist (x + Δ) ℓ = 0 := by exact_mod_cast h
    exact hℓ (Nat.eq_of_dist_eq_zero h0 ▸ mem_shift.mpr ⟨x, hx, rfl⟩)
  have hT : ∀ x ∈ L, (((x + Δ).factorial : ℝ) / x.factorial) ≠ 0 := fun x _ => by
    have := Nat.factorial_pos x; have := Nat.factorial_pos (x + Δ); positivity
  rw [hset_step hℓ]
  push_cast
  have hH : (hset L : ℝ) ≠ 0 := by exact_mod_cast (hset_pos L).ne'
  have hS : (ℓ.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos ℓ).ne'
  rw [Real.log_div (by
      refine mul_ne_zero (mul_ne_zero hH (prod_ne_zero_iff.mpr hT)) hS)
      (prod_ne_zero_iff.mpr hd),
    Real.log_mul (mul_ne_zero hH (prod_ne_zero_iff.mpr hT)) hS,
    Real.log_mul hH (prod_ne_zero_iff.mpr hT), Real.log_prod hT, Real.log_prod hd]
  ring

end RMT.StringInsertion
