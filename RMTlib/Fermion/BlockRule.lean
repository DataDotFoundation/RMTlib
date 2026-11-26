import Mathlib

/-!
# The block rule: block insertion as a matching

The doubled block `[d] = {d−1, d−3, …, 1−d}` is the set of `d` integers of the parity of `d − 1`
lying strictly inside `(−d, d)`.  Inserting it into a configuration of coloured particles `a`
(colours `s`) gives a configuration `b` (colours `t`) — colours kept above `0`, flipped below `0` —
exactly when every particle of `a` is matched with a particle of `b` at the same site with
`t·s·site > d`, and every other particle of `b` lies inside the block
(`blockInsert_iff_matched`).

This is the a1 certificate of RH-Dual's roadmap (`bridge/links/roadmap-a1-a3.md`, RH-Dual#262).
-/

open Finset

namespace RMT.Fermion.Block

/-- The doubled block `[d] = {d−1, d−3, …, 1−d}`. -/
def dblock (d : ℕ) : Finset ℤ := (Finset.range d).image fun b : ℕ => (d : ℤ) - 1 - 2 * b

/-- Membership in the doubled block: inside `(−d, d)` and of the parity of `d − 1`. -/
theorem mem_dblock {d : ℕ} {x : ℤ} : x ∈ dblock d ↔ |x| < d ∧ Even (x + d - 1) := by
  simp only [dblock, mem_image, mem_range]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨abs_lt.2 ⟨by omega, by omega⟩, ⟨(d : ℤ) - 1 - b, by ring⟩⟩
  · rintro ⟨h, k, hk⟩
    obtain ⟨h1, h2⟩ := abs_lt.1 h
    refine ⟨(d - 1 - k).toNat, by omega, by omega⟩

/-- The doubled block has `d` elements. -/
theorem card_dblock (d : ℕ) : (dblock d).card = d := by
  rw [dblock, card_image_of_injective _ (fun x y h => by simpa using h), card_range]

/-- Summing over a set disjoint from the doubled block, with the block adjoined. -/
theorem sum_union_dblock {M : Type*} [AddCommMonoid M] {A : Finset ℤ} {d : ℕ}
    (hA : Disjoint A (dblock d)) (φ : ℤ → M) :
    ∑ x ∈ A ∪ dblock d, φ x = ∑ x ∈ A, φ x + ∑ b ∈ range d, φ ((d : ℤ) - 1 - 2 * b) := by
  rw [sum_union hA, dblock, sum_image (fun x _ y _ h => by simpa using h)]

private theorem units_mul_self (u : ℤˣ) : ((u * u : ℤˣ) : ℤ) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

private theorem units_val_eq_one_or (u : ℤˣ) : (u : ℤ) = 1 ∨ (u : ℤ) = -1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- **Block insertion = matching.** Coloured particles `a` (colours `s`) on `C` and `b` (colours `t`) on `R`,
with `|R| = |C| + d`, distinct positions, and `b` of the parity of `d − 1`. Then `b` is `a` with the block `[d]`
inserted, colours kept above `0` and flipped below `0`, if and only if every particle of `a` is matched with a
particle of `b` at the same site, with `t·s·site > d`, and every other particle of `b` lies inside the block. -/
theorem blockInsert_iff_matched {C R : Type*} [Fintype C] [Fintype R]
    {s : C → ℤˣ} {t : R → ℤˣ} {a : C → ℤ} {b : R → ℤ} {d : ℕ}
    (hcard : Fintype.card R = Fintype.card C + d)
    (ha : a.Injective) (hb : b.Injective) (hpar : ∀ r, Even (b r + d - 1)) :
    (Finset.univ.image b = Finset.univ.image a ∪ dblock d ∧
      (∀ c r, a c = b r → 0 < a c → s c = t r) ∧
      (∀ c r, a c = b r → a c < 0 → s c = -t r)) ↔
    ((∀ r, (∃ c, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r) ∨ |b r| < d) ∧
      ∀ c, ∃ r, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r) := by
  have hcb : (univ.image b).card = Fintype.card C + d := by
    rw [card_image_of_injective _ hb, card_univ, hcard]
  have hca : (univ.image a).card = Fintype.card C := by
    rw [card_image_of_injective _ ha, card_univ]
  constructor
  · rintro ⟨himg, hpos, hneg⟩
    -- the union is disjoint, by counting
    have hdisj : Disjoint (univ.image a) (dblock d) := by
      have h := card_union_add_card_inter (univ.image a) (dblock d)
      rw [← himg, hcb, hca, card_dblock] at h
      exact disjoint_iff_inter_eq_empty.2 (card_eq_zero.1 (by omega))
    -- a matched site is outside the block, hence of absolute value `> d`
    have key : ∀ c r, b r = a c → (d : ℤ) < (t r * s c : ℤˣ) * b r := by
      intro c r hbr
      have hnot : b r ∉ dblock d := fun hm =>
        disjoint_left.1 hdisj (mem_image_of_mem a (mem_univ c)) (hbr ▸ hm)
      have hgt : (d : ℤ) < |b r| := by
        rw [mem_dblock, not_and] at hnot
        have := hpar r
        rcases lt_trichotomy |b r| d with h | h | h
        · exact absurd this (hnot h)
        · -- `|b r| = d` contradicts the parity of `d − 1`
          obtain ⟨k, hk⟩ := this
          rcases abs_eq (by positivity : (0 : ℤ) ≤ d) |>.1 h with h' | h' <;> omega
        · exact h
      rcases lt_trichotomy (b r) 0 with h | h | h
      · rw [hneg c r hbr.symm (hbr ▸ h), Units.val_mul, Units.val_neg, abs_of_neg h] at *
        rcases units_val_eq_one_or (t r) with h1 | h1 <;> rw [h1] at * <;> linarith
      · rw [h] at hgt; simp at hgt; omega
      · rw [hpos c r hbr.symm (hbr ▸ h), units_mul_self, one_mul]
        rwa [abs_of_pos h] at hgt
    refine ⟨fun r => ?_, fun c => ?_⟩
    · have hr : b r ∈ univ.image a ∪ dblock d := himg ▸ mem_image_of_mem b (mem_univ r)
      rcases mem_union.1 hr with h | h
      · obtain ⟨c, -, hc⟩ := mem_image.1 h
        exact Or.inl ⟨c, hc.symm, key c r hc.symm⟩
      · exact Or.inr (mem_dblock.1 h).1
    · have hc : a c ∈ univ.image b := himg ▸ mem_union_left _ (mem_image_of_mem a (mem_univ c))
      obtain ⟨r, -, hr⟩ := mem_image.1 hc
      exact ⟨r, hr, key c r hr⟩
  · rintro ⟨hR, hC⟩
    -- a matched pair has `t r * s c = sign (b r)`
    have hmatch : ∀ c r, a c = b r → (d : ℤ) < (t r * s c : ℤˣ) * b r := by
      intro c r h
      obtain ⟨r', hr', hlt⟩ := hC c
      rwa [hb (hr'.trans h)] at hlt
    have hsub : univ.image b ⊆ univ.image a ∪ dblock d := by
      intro x hx
      obtain ⟨r, -, rfl⟩ := mem_image.1 hx
      rcases hR r with ⟨c, hc, -⟩ | h
      · exact mem_union_left _ (hc ▸ mem_image_of_mem a (mem_univ c))
      · exact mem_union_right _ (mem_dblock.2 ⟨h, hpar r⟩)
    have hle : (univ.image a ∪ dblock d).card ≤ (univ.image b).card :=
      calc (univ.image a ∪ dblock d).card ≤ (univ.image a).card + (dblock d).card :=
            card_union_le _ _
        _ = (univ.image b).card := by rw [hca, card_dblock, hcb]
    refine ⟨eq_of_subset_of_card_le hsub hle, fun c r h hpos => ?_, fun c r h hneg => ?_⟩
    · have := hmatch c r h
      rw [← h] at this
      rcases Int.units_eq_one_or (t r) with h1 | h1 <;>
        rcases Int.units_eq_one_or (s c) with h2 | h2 <;> rw [h1, h2] at this ⊢ <;>
        simp at this ⊢ <;> omega
    · have := hmatch c r h
      rw [← h] at this
      rcases Int.units_eq_one_or (t r) with h1 | h1 <;>
        rcases Int.units_eq_one_or (s c) with h2 | h2 <;> rw [h1, h2] at this ⊢ <;>
        simp at this ⊢ <;> omega

end RMT.Fermion.Block
