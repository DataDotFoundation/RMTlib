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
for the translation down). **Draining** (`hset_drain`): `H` of the hole side never increases, for any
translation `Δ ≥ 1` and removal of the lowest hole, proved factor by factor.
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

/-! ### Draining: the hole side never grows -/

theorem factorial_mul_le_factorial_add {x Δ : ℕ} (hΔ : 1 ≤ Δ) :
    x.factorial * (x + Δ) ≤ (x + Δ).factorial := by
  obtain ⟨d, rfl⟩ : ∃ d, Δ = d + 1 := ⟨Δ - 1, by omega⟩
  rw [← add_assoc, Nat.factorial_succ, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.factorial_le (Nat.le_add_right x d))

/-- **Draining** (RMTlib#72, RH-Dual's lane-C target). On the hole side a lift removes the hole that
crossed, the lowest one `ℓ`, and translates the others down by `Δ ≥ 1`. Read upwards: the old hole
set is `insert ℓ (L + Δ)` with `ℓ` below every other hole, and the new one is `L`. Then `H` never
grows: `H(L) ≤ H(insert ℓ (L + Δ))`.

The proof is factor by factor, and says why both pieces are needed together: the removal alone can
raise `H`, but each remaining hole's distance to the removed one, `x + Δ − ℓ`, is at most its own
position `x + Δ`, and the translation divides by `(x + Δ)!/x! ≥ x + Δ`. -/
theorem hset_drain {L : Finset ℕ} {Δ ℓ : ℕ} (hΔ : 1 ≤ Δ) (hℓ : ∀ x ∈ L, ℓ < x + Δ) :
    hset L ≤ hset (insert ℓ (shift L Δ)) := by
  have hℓ' : ℓ ∉ shift L Δ := by
    rw [mem_shift]; rintro ⟨x, hx, h⟩; have := hℓ x hx; omega
  rw [hset_step hℓ']
  have hB : 0 < ∏ x ∈ L, (Nat.dist (x + Δ) ℓ : ℚ) := prod_pos fun x hx => by
    have := hℓ x hx
    have : Nat.dist (x + Δ) ℓ ≠ 0 := fun h => by have := Nat.eq_of_dist_eq_zero h; omega
    positivity
  have hBA : ∏ x ∈ L, (Nat.dist (x + Δ) ℓ : ℚ) ≤
      ∏ x ∈ L, ((x + Δ).factorial : ℚ) / x.factorial := by
    refine prod_le_prod (fun x _ => by positivity) fun x hx => ?_
    have h1 : Nat.dist (x + Δ) ℓ ≤ x + Δ := by
      have := hℓ x hx
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]; omega
    have h2 := factorial_mul_le_factorial_add (x := x) hΔ
    have hx0 : (0 : ℚ) < x.factorial := by exact_mod_cast Nat.factorial_pos x
    rw [le_div_iff₀ hx0]
    calc (Nat.dist (x + Δ) ℓ : ℚ) * x.factorial ≤ ((x + Δ : ℕ) : ℚ) * x.factorial := by
          gcongr
      _ ≤ (x + Δ).factorial := by rw [mul_comm]; exact_mod_cast h2
  have hS : (1 : ℚ) ≤ ℓ.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero ℓ)
  have hH := hset_pos L
  rw [le_div_iff₀ hB, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hH.le
  calc ∏ x ∈ L, (Nat.dist (x + Δ) ℓ : ℚ) ≤ ∏ x ∈ L, ((x + Δ).factorial : ℚ) / x.factorial := hBA
    _ = (∏ x ∈ L, ((x + Δ).factorial : ℚ) / x.factorial) * 1 := (mul_one _).symm
    _ ≤ (∏ x ∈ L, ((x + Δ).factorial : ℚ) / x.factorial) * ℓ.factorial := by
        gcongr

end RMT.StringInsertion

/-! ### Two crossings at once (move M6) -/

namespace RMT.StringInsertion

open Finset

theorem shift_shift (L : Finset ℕ) (a b : ℕ) : shift (shift L a) b = shift L (a + b) := by
  ext y
  simp only [mem_shift]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, by ring⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x + a, ⟨x, hx, rfl⟩, by ring⟩

theorem not_mem_shift_add {L : Finset ℕ} {Δ b ℓ : ℕ} (h : ℓ ∉ shift L Δ) :
    ℓ + b ∉ shift L (Δ + b) := by
  rw [mem_shift]; rintro ⟨x, hx, hxe⟩
  exact h (mem_shift.mpr ⟨x, hx, by omega⟩)

/-- **Inserting one charge, in logarithms.** -/
theorem log_hset_insert {M : Finset ℕ} {ℓ : ℕ} (hℓ : ℓ ∉ M) :
    Real.log (hset (insert ℓ M)) =
      Real.log (hset M) + Real.log ℓ.factorial - ∑ y ∈ M, Real.log (Nat.dist y ℓ : ℝ) := by
  have hd : ∀ y ∈ M, (Nat.dist y ℓ : ℝ) ≠ 0 := by
    intro y hy h
    have h0 : Nat.dist y ℓ = 0 := by exact_mod_cast h
    exact hℓ (Nat.eq_of_dist_eq_zero h0 ▸ hy)
  have hH : (hset M : ℝ) ≠ 0 := by exact_mod_cast (hset_pos M).ne'
  have hS : (ℓ.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos ℓ).ne'
  rw [hset_insert hℓ]
  push_cast
  rw [Real.log_div (mul_ne_zero hH hS) (prod_ne_zero_iff.mpr hd), Real.log_mul hH hS,
    Real.log_prod hd]

/-- **The merged step** (M6): translate by `Δ`, then insert two charges `ℓ₁`, `ℓ₂`. The two-body
part gains exactly one cross term `−log |ℓ₁ − ℓ₂|` between the two newcomers; everything else is the
sum of the single steps' terms (RH-Dual #102 computed this; here it is an identity). -/
theorem log_hset_two_step {L : Finset ℕ} {Δ ℓ₁ ℓ₂ : ℕ} (h₁ : ℓ₁ ∉ shift L Δ)
    (h₂ : ℓ₂ ∉ insert ℓ₁ (shift L Δ)) :
    Real.log (hset (insert ℓ₂ (insert ℓ₁ (shift L Δ)))) - Real.log (hset L) =
      (∑ x ∈ L, Real.log (((x + Δ).factorial : ℝ) / x.factorial)) +
      Real.log ℓ₁.factorial + Real.log ℓ₂.factorial -
      (∑ x ∈ L, Real.log (Nat.dist (x + Δ) ℓ₁ : ℝ)) -
      (∑ x ∈ L, Real.log (Nat.dist (x + Δ) ℓ₂ : ℝ)) -
      Real.log (Nat.dist ℓ₁ ℓ₂ : ℝ) := by
  have step := log_hset_step h₁
  rw [log_hset_insert h₂, sum_insert h₁]
  have hmap : ∑ y ∈ shift L Δ, Real.log (Nat.dist y ℓ₂ : ℝ) =
      ∑ x ∈ L, Real.log (Nat.dist (x + Δ) ℓ₂ : ℝ) := by
    simp [shift, sum_map]
  rw [hmap]
  linarith

end RMT.StringInsertion

/-! ### The step as a function of the gap (move M4) -/

namespace RMT.StringInsertion

open Finset

/-- **The step in tower coordinates.** On the tower the crossing charge lands at `ℓ = Δ − g`, where
`g = c − z ≥ 1` is fixed by the crossing point `z` and the band, so the distance from each old
particle `x + Δ` to it is `x + g`, **independent of `Δ`**. Hence only the one-body terms depend on
the spacing: `Δ log H = Σ log((x+Δ)!/x!) + log (Δ − g)! − Σ log (x + g)`. -/
theorem log_hset_step_gap {L : Finset ℕ} {g Δ : ℕ} (hg : 1 ≤ g) (hgΔ : g ≤ Δ) :
    Real.log (hset (insert (Δ - g) (shift L Δ))) - Real.log (hset L) =
      (∑ x ∈ L, Real.log (((x + Δ).factorial : ℝ) / x.factorial)) +
      Real.log (Δ - g).factorial -
      ∑ x ∈ L, Real.log ((x + g : ℕ) : ℝ) := by
  have hℓ : Δ - g ∉ shift L Δ := by
    rw [mem_shift]; rintro ⟨x, _, hx⟩; omega
  have hdist : ∀ x : ℕ, Nat.dist (x + Δ) (Δ - g) = x + g := by
    intro x; unfold Nat.dist; omega
  rw [log_hset_step hℓ]
  simp only [hdist]

/-- **The step grows with the spacing** (M4): for a fixed configuration and crossing offset `g`,
`Δ log H` is monotone in the gap `Δ`. The two-body part does not move; the translation and the
self-energy both grow. -/
theorem log_hset_step_gap_mono {L : Finset ℕ} {g Δ Δ' : ℕ} (hg : 1 ≤ g) (hgΔ : g ≤ Δ)
    (hΔ : Δ ≤ Δ') :
    Real.log (hset (insert (Δ - g) (shift L Δ))) - Real.log (hset L) ≤
      Real.log (hset (insert (Δ' - g) (shift L Δ'))) - Real.log (hset L) := by
  rw [log_hset_step_gap hg hgΔ, log_hset_step_gap hg (hgΔ.trans hΔ)]
  have hT : ∑ x ∈ L, Real.log (((x + Δ).factorial : ℝ) / x.factorial) ≤
      ∑ x ∈ L, Real.log (((x + Δ').factorial : ℝ) / x.factorial) := by
    refine sum_le_sum fun x _ => ?_
    have h0 : (0 : ℝ) < x.factorial := by exact_mod_cast Nat.factorial_pos x
    have h1 : (0 : ℝ) < (x + Δ).factorial := by exact_mod_cast Nat.factorial_pos _
    refine Real.log_le_log (by positivity) ?_
    refine div_le_div_of_nonneg_right ?_ h0.le
    exact_mod_cast Nat.factorial_le (by omega)
  have hS : Real.log (Δ - g).factorial ≤ Real.log (Δ' - g).factorial := by
    refine Real.log_le_log (by exact_mod_cast Nat.factorial_pos _) ?_
    exact_mod_cast Nat.factorial_le (by omega)
  linarith

end RMT.StringInsertion

/-! ### The two-body part is small against the translation (RMTlib#79, RH-Dual #128) -/

namespace RMT.StringInsertion

open Finset

/-- **Pairing the rising factorial**: `(x + Δ)^Δ ≤ ((x+1)(x+2)⋯(x+Δ))²`. Pair the factor `x + u + 1`
with `x + Δ − u`: each pair is at least `x + Δ`. -/
theorem pow_le_ascFactorial_sq (x Δ : ℕ) : (x + Δ) ^ Δ ≤ ((x + 1).ascFactorial Δ) ^ 2 := by
  rw [Nat.ascFactorial_eq_prod_range, sq]
  nth_rewrite 2 [← prod_range_reflect]
  rw [← prod_mul_distrib]
  calc (x + Δ) ^ Δ = ∏ _u ∈ range Δ, (x + Δ) := by rw [prod_const, card_range]
    _ ≤ ∏ u ∈ range Δ, ((x + 1 + u) * (x + 1 + (Δ - 1 - u))) := by
        refine prod_le_prod' fun u hu => ?_
        have hu := mem_range.mp hu
        have h1 : x + 1 + (Δ - 1 - u) = x + Δ - u := by omega
        rw [h1]
        nlinarith [Nat.sub_add_cancel (show u ≤ x + Δ by omega)]

/-- `(x + Δ)! / x!` is the rising factorial `(x+1)⋯(x+Δ)`. -/
theorem factorial_div_factorial_eq_ascFactorial (x Δ : ℕ) :
    ((x + Δ).factorial : ℝ) / x.factorial = ((x + 1).ascFactorial Δ : ℕ) := by
  rw [← Nat.factorial_mul_ascFactorial x Δ]
  have : (x.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos x).ne'
  push_cast
  field_simp

/-- **Per particle**: `log (x + g) ≤ (2/Δ) · log ((x+Δ)!/x!)` for `1 ≤ g ≤ Δ`, every `x`. -/
theorem log_add_le_two_div_mul {x g Δ : ℕ} (hg : 1 ≤ g) (hgΔ : g ≤ Δ) :
    Real.log ((x + g : ℕ) : ℝ) ≤
      2 / Δ * Real.log (((x + Δ).factorial : ℝ) / x.factorial) := by
  have hΔ : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  rw [factorial_div_factorial_eq_ascFactorial]
  have hpos : (0 : ℝ) < ((x + 1).ascFactorial Δ : ℕ) := by
    exact_mod_cast Nat.ascFactorial_pos x Δ
  have h1 : Real.log ((x + g : ℕ) : ℝ) ≤ Real.log ((x + Δ : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < x + g by omega)) (by exact_mod_cast (by omega))
  have h2 : (Δ : ℝ) * Real.log ((x + Δ : ℕ) : ℝ) ≤ 2 * Real.log ((x + 1).ascFactorial Δ : ℕ) := by
    have e2 := Real.log_pow (((x + 1).ascFactorial Δ : ℕ) : ℝ) 2
    push_cast at e2
    rw [← Real.log_pow, ← e2]
    have hxΔ : (0 : ℝ) < ((x + Δ : ℕ) : ℝ) := by exact_mod_cast (show 0 < x + Δ by omega)
    refine Real.log_le_log (by positivity) ?_
    exact_mod_cast pow_le_ascFactorial_sq x Δ
  rw [div_mul_eq_mul_div, le_div_iff₀ hΔ]
  nlinarith

/-- **The two-body part is at most `2/Δ` of the translation**, for every finite Maya set: with the
step in tower coordinates (`log_hset_step_gap`), `|V| = Σ log (x + g) ≤ (2/Δ) · T`. -/
theorem log_hset_step_gap_V_le {L : Finset ℕ} {g Δ : ℕ} (hg : 1 ≤ g) (hgΔ : g ≤ Δ) :
    ∑ x ∈ L, Real.log ((x + g : ℕ) : ℝ) ≤
      2 / Δ * ∑ x ∈ L, Real.log (((x + Δ).factorial : ℝ) / x.factorial) := by
  rw [mul_sum]
  exact sum_le_sum fun x _ => log_add_le_two_div_mul hg hgΔ

/-- **The overshoot is `O(1/Δ)`** (RMTlib#79; RH-Dual #128). The step is at least `(1 − 2/Δ)` times its
translation part: `(1 − 2/Δ) · T ≤ Δ log H`. With `Δ ≥ t + 3` on the proof's tower (RH-Dual's
identification), the translation overshoots the step by at most a factor `1/(1 − 2/(t+3))`,
uniformly in the ranks, the level and the positions. -/
theorem translation_le_step {L : Finset ℕ} {g Δ : ℕ} (hg : 1 ≤ g) (hgΔ : g ≤ Δ) :
    (1 - 2 / (Δ : ℝ)) * ∑ x ∈ L, Real.log (((x + Δ).factorial : ℝ) / x.factorial) ≤
      Real.log (hset (insert (Δ - g) (shift L Δ))) - Real.log (hset L) := by
  rw [log_hset_step_gap hg hgΔ]
  have hS : 0 ≤ Real.log ((Δ - g).factorial : ℝ) := Real.log_natCast_nonneg _
  have hV := log_hset_step_gap_V_le (L := L) hg hgΔ
  nlinarith

end RMT.StringInsertion

