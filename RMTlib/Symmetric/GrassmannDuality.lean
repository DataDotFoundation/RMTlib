import RMTlib.Symmetric.FominMaya

/-!
# ω on a Maya window is Grassmannian duality (#142, target 1)

A Maya set in the window `[L, M − 1]` of `n = M − L` sites is a `k`-subset, i.e. a Schubert cell of
`Gr(k, n)` (over `𝔽₁`: coordinate subspaces). `ω` (`conjBox`: the holes, reflected by `y ↦ −1 − y`,
in the window `[−M, −L − 1]`) is:

* `conjBox_subset`, `card_conjBox`: a map to `(n − k)`-subsets of the reflected window
  (`Gr(k, n) → Gr(n − k, n)`);
* `conjBox_conjBox`: an involution;
* `conjBox_subset_iff`: **inclusion-reversing**, `S ⊆ T ↔ ω T ⊆ ω S`: the incidence of projective
  duality;
* `conjBox_three`: in a 3-site window, `ω` sends points (one particle) to lines (two particles) and
  back, reversing incidence: **point–line duality of `ℙ²` over `𝔽₁`**, the pairing of rows 2 and 6
  of the `ℙ¹` inventory (RMTlib#129, #142) into a `ℙ²`.

This is the box ω of `fominEigen_conjBox` (particle–hole duality exchanging the two walls), now read
as projective duality.
-/

open Finset

namespace RMT.Symmetric.Corners

/-- `ω` lands in the reflected window. -/
theorem conjBox_subset (L M : ℤ) (S : Finset ℤ) : conjBox L M S ⊆ Icc (-M) (-L - 1) := by
  intro x hx
  simp only [conjBox, mem_image, mem_sdiff, mem_Icc] at hx
  obtain ⟨y, ⟨⟨h1, h2⟩, -⟩, rfl⟩ := hx
  simp only [mem_Icc]; omega

theorem mem_conjBox {L M : ℤ} {S : Finset ℤ} {x : ℤ} :
    x ∈ conjBox L M S ↔ -1 - x ∈ Icc L (M - 1) ∧ -1 - x ∉ S := by
  simp only [conjBox, mem_image, mem_sdiff]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · rintro h; exact ⟨-1 - x, h, by ring⟩

/-- **`ω` is an involution**: the dual of the dual window gives back `S`. -/
theorem conjBox_conjBox {L M : ℤ} {S : Finset ℤ} (hS : S ⊆ Icc L (M - 1)) :
    conjBox (-M) (-L) (conjBox L M S) = S := by
  ext x
  have e : -1 - (-1 - x) = x := by ring
  rw [mem_conjBox, mem_conjBox, e]
  simp only [mem_Icc, not_and, not_not]
  constructor
  · rintro ⟨⟨h1, h2⟩, h⟩; exact h ⟨by omega, by omega⟩
  · intro hx
    have := hS hx
    simp only [mem_Icc] at this
    exact ⟨⟨by omega, by omega⟩, fun _ => hx⟩

/-- **`ω` reverses inclusion**: `S ⊆ T` iff `ω T ⊆ ω S`, the incidence of projective duality. -/
theorem conjBox_subset_iff {L M : ℤ} {S T : Finset ℤ} (hS : S ⊆ Icc L (M - 1))
    (hT : T ⊆ Icc L (M - 1)) : S ⊆ T ↔ conjBox L M T ⊆ conjBox L M S := by
  constructor
  · intro h x hx
    rw [mem_conjBox] at hx ⊢
    exact ⟨hx.1, fun hs => hx.2 (h hs)⟩
  · intro h
    rw [← conjBox_conjBox hS, ← conjBox_conjBox hT]
    intro x hx
    rw [mem_conjBox] at hx ⊢
    exact ⟨hx.1, fun hs => hx.2 (h hs)⟩

/-- **`ω` sends `k` particles to `n − k`**, with `n = M − L` sites: `Gr(k, n) ↔ Gr(n − k, n)`. -/
theorem card_conjBox {L M : ℤ} {S : Finset ℤ} (hS : S ⊆ Icc L (M - 1)) (hLM : L ≤ M) :
    (conjBox L M S).card + S.card = (M - L).toNat := by
  rw [conjBox, card_image_of_injective _ (fun a b (h : -1 - a = -1 - b) => by omega),
    card_sdiff_of_subset hS, Int.card_Icc]
  have := card_le_card hS
  rw [Int.card_Icc] at this
  omega

/-- **Point–line duality of the plane over `𝔽₁`**: in a 3-site window, `ω` sends the points
(one particle) to lines (two particles) and back, reversing incidence. -/
theorem conjBox_three {L : ℤ} {p ℓ : Finset ℤ} (hp : p ⊆ Icc L (L + 2)) (hℓ : ℓ ⊆ Icc L (L + 2))
    (hp1 : p.card = 1) (hℓ2 : ℓ.card = 2) :
    (conjBox L (L + 3) p).card = 2 ∧ (conjBox L (L + 3) ℓ).card = 1 ∧
      (p ⊆ ℓ ↔ conjBox L (L + 3) ℓ ⊆ conjBox L (L + 3) p) := by
  have w : Icc L (L + 3 - 1) = Icc L (L + 2) := by congr 1; ring
  have hp' : p ⊆ Icc L (L + 3 - 1) := w ▸ hp
  have hℓ' : ℓ ⊆ Icc L (L + 3 - 1) := w ▸ hℓ
  have c1 := card_conjBox hp' (by omega)
  have c2 := card_conjBox hℓ' (by omega)
  rw [show (L + 3 - L).toNat = 3 by omega] at c1 c2
  exact ⟨by omega, by omega, conjBox_subset_iff hp' hℓ'⟩

end RMT.Symmetric.Corners
