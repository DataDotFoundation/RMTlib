import RMTlib.Symmetric.WeightedCauchy
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Partition statistics, and how one wall breaks `ω`

The statistics read off a shape fall into two families (RMTlib#13, #53):

* **edge statistics**, such as `firstRow μ = λ₁` and `numRows μ = ℓ(λ)`. Under Plancherel they fluctuate
  on the scale `n^{1/6}` (Airy, Tracy–Widom), or feel a hard edge (Bessel) when a wall is close.
* **global statistics**, such as the content moments `Σ_□ c(□)^k`. Under Plancherel they have Gaussian
  fluctuations (Kerov).

`ω` (`μ ↦ μᵀ`) exchanges `firstRow` and `numRows` (`firstRow_transpose`) and acts on content moments by
the sign `(−1)^k` (`contentMoment_transpose`). So `firstRow − numRows` and the odd content moments are
**`ω`-odd**, and the even content moments are **`ω`-even**.

## The model of symmetry breaking

Take a finite family `S` of shapes closed under `ω` (all shapes of size `n`, say) and an `ω`-even
weight `w` (Plancherel `(f^λ)²` is one). Then:

* **no wall**: every `ω`-odd statistic has total weight zero (`sum_odd_eq_zero`).
* **one wall** (`numRows ≤ N`: the boson's wall, finitely many variables): `ω` maps the walled family
  onto the family with the *other* wall (`firstRow ≤ N`, the fermion's), which is a different family
  (`sum_bosonWall_transpose`). That is how the wall breaks `ω`.
* **where the breaking lives**: the weighted sum of an `ω`-odd statistic over the walled family is
  carried exactly by the shapes that cross the other wall, `numRows ≤ N < firstRow`
  (`sum_bosonWall_odd`). The shapes inside the `N × N` box contribute nothing.
* **two walls restore `ω`**: on the box `numRows ≤ N ∧ firstRow ≤ N` the total is zero again
  (`sum_box_odd_eq_zero`). This is the symmetry behind `BoxComplementSymmetry` in
  `RMT.Edges` (there the box is `k × N`, and the mirror is box complement rather than `ω`).

In the content form of the walls (`RMT.Symmetric.contentProd_nat_add_eq_zero_iff`: `∏ (N + c) = 0`
exactly when `ℓ(λ) > N`), a weight such as `∏ (N + c)²` implements the boson's wall, and its
`ω`-image is `∏ (N − c)²`, the fermion's. The theorems below need only that the wall is a filter.

All statements are for an arbitrary commutative ring `R`, except where `2` must be cancelled
(`CharZero`, no zero divisors).
-/

namespace RMT.Edges

open Finset RMT.Symmetric

/-! ## Statistics and how `ω` acts on them -/

/-- The top row `λ₁`. -/
def firstRow (μ : YoungDiagram) : ℕ := μ.rowLen 0

/-- The number of rows `ℓ(λ)`. -/
def numRows (μ : YoungDiagram) : ℕ := μ.colLen 0

@[simp] theorem firstRow_transpose (μ : YoungDiagram) : firstRow μ.transpose = numRows μ :=
  μ.rowLen_transpose 0

@[simp] theorem numRows_transpose (μ : YoungDiagram) : numRows μ.transpose = firstRow μ :=
  μ.colLen_transpose 0

/-- The `k`-th content moment `Σ_{□ ∈ μ} c(□)^k`. `k = 0` counts boxes, and `k = 1` is the content
sum, `C(n, 2) · χ^λ(transposition) / f^λ`. -/
def contentMoment (k : ℕ) (μ : YoungDiagram) : ℤ := ∑ c ∈ μ.cells, content c ^ k

/-- **`ω` on content moments**: the sign `(−1)^k`. -/
theorem contentMoment_transpose (k : ℕ) (μ : YoungDiagram) :
    contentMoment k μ.transpose = (-1) ^ k * contentMoment k μ := by
  unfold contentMoment
  rw [mul_sum]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simpa [YoungDiagram.mem_cells, YoungDiagram.mem_transpose] using hc
  · intro c hc
    simpa [YoungDiagram.mem_cells, YoungDiagram.mem_transpose] using hc
  · intro c _
    simp
  · intro c _
    simp
  · intro c _
    rw [content_swap, ← mul_pow]
    norm_num

/-- An `ω`-even function of shapes. -/
def OmegaEven {R : Type*} (f : YoungDiagram → R) : Prop := ∀ μ, f μ.transpose = f μ

/-- An `ω`-odd function of shapes. -/
def OmegaOdd {R : Type*} [Neg R] (f : YoungDiagram → R) : Prop := ∀ μ, f μ.transpose = -f μ

/-- `λ₁ − ℓ(λ)` is `ω`-odd: the simplest statistic a wall can bias. -/
theorem omegaOdd_firstRow_sub_numRows :
    OmegaOdd fun μ => (firstRow μ : ℤ) - numRows μ := by
  intro μ
  simp

/-- Odd content moments are `ω`-odd. -/
theorem omegaOdd_contentMoment {k : ℕ} (hk : Odd k) : OmegaOdd (contentMoment k) := by
  intro μ
  rw [contentMoment_transpose, hk.neg_one_pow, neg_one_mul]

/-- Even content moments are `ω`-even. -/
theorem omegaEven_contentMoment {k : ℕ} (hk : Even k) : OmegaEven (contentMoment k) := by
  intro μ
  rw [contentMoment_transpose, hk.neg_one_pow, one_mul]

/-! ## Walls -/

variable {R : Type*} [CommRing R]

/-- Reindex a sum over an `ω`-closed family by `ω`, restricting by `p` on one side and by `p ∘ ω` on
the other. -/
theorem sum_filter_transpose (S : Finset YoungDiagram) (hS : ∀ μ ∈ S, μ.transpose ∈ S)
    (p : YoungDiagram → Prop) [DecidablePred p] (g : YoungDiagram → R) :
    ∑ μ ∈ S with p μ, g μ.transpose = ∑ μ ∈ S with p μ.transpose, g μ := by
  refine Finset.sum_nbij' YoungDiagram.transpose YoungDiagram.transpose ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [mem_filter] at hμ ⊢
    exact ⟨hS μ hμ.1, by simpa using hμ.2⟩
  · intro μ hμ
    simp only [mem_filter] at hμ ⊢
    exact ⟨hS μ hμ.1, hμ.2⟩
  · intro μ _
    simp
  · intro μ _
    simp
  · intro μ _
    rfl

/-- **`ω` exchanges the walls.** Over an `ω`-closed family, with an `ω`-even weight `w`, summing
`f ∘ ω` behind the boson's wall (`ℓ(λ) ≤ N`) is summing `f` behind the fermion's wall (`λ₁ ≤ N`). -/
theorem sum_bosonWall_transpose (S : Finset YoungDiagram) (hS : ∀ μ ∈ S, μ.transpose ∈ S)
    (N : ℕ) (w f : YoungDiagram → R) (hw : OmegaEven w) :
    ∑ μ ∈ S with numRows μ ≤ N, w μ * f μ.transpose =
      ∑ μ ∈ S with firstRow μ ≤ N, w μ * f μ := by
  have := sum_filter_transpose S hS (fun μ => numRows μ ≤ N) (fun μ => w μ * f μ)
  simp only [numRows_transpose] at this
  rw [← this]
  refine sum_congr rfl fun μ _ => ?_
  rw [hw]

/-- **The two corners cancel.** The shapes beyond the box on one side are the `ω`-image of those on
the other: for an `ω`-odd statistic their weighted sums are opposite. -/
theorem sum_corner_odd (S : Finset YoungDiagram) (hS : ∀ μ ∈ S, μ.transpose ∈ S)
    (N : ℕ) (w f : YoungDiagram → R) (hw : OmegaEven w) (hf : OmegaOdd f) :
    ∑ μ ∈ S with firstRow μ ≤ N ∧ N < numRows μ, w μ * f μ =
      -∑ μ ∈ S with numRows μ ≤ N ∧ N < firstRow μ, w μ * f μ := by
  have := sum_filter_transpose S hS (fun μ => numRows μ ≤ N ∧ N < firstRow μ)
    (fun μ => w μ * f μ)
  simp only [numRows_transpose, firstRow_transpose] at this
  rw [← this, ← sum_neg_distrib]
  refine sum_congr rfl fun μ _ => ?_
  rw [hw, hf, mul_neg]

section CharZero

variable [IsDomain R] [CharZero R]

private theorem eq_zero_of_eq_neg {x : R} (h : x = -x) : x = 0 := by
  have h2 : (2 : R) * x = 0 := by rw [two_mul]; nth_rewrite 1 [h]; exact neg_add_cancel x
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · exact h

/-- **No wall, no bias.** Over an `ω`-closed family with an `ω`-even weight, an `ω`-odd statistic
has total weight zero. -/
theorem sum_odd_eq_zero (S : Finset YoungDiagram) (hS : ∀ μ ∈ S, μ.transpose ∈ S)
    (w f : YoungDiagram → R) (hw : OmegaEven w) (hf : OmegaOdd f) :
    ∑ μ ∈ S, w μ * f μ = 0 := by
  have := sum_filter_transpose S hS (fun _ => True) (fun μ => w μ * f μ)
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial)] at this
  refine eq_zero_of_eq_neg ?_
  rw [← sum_neg_distrib]
  nth_rewrite 1 [← this]
  refine sum_congr rfl fun μ _ => ?_
  rw [hw, hf, mul_neg]

/-- **Two walls restore `ω`.** In the `N × N` box an `ω`-odd statistic has total weight zero. -/
theorem sum_box_odd_eq_zero (S : Finset YoungDiagram) (hS : ∀ μ ∈ S, μ.transpose ∈ S)
    (N : ℕ) (w f : YoungDiagram → R) (hw : OmegaEven w) (hf : OmegaOdd f) :
    ∑ μ ∈ S with numRows μ ≤ N ∧ firstRow μ ≤ N, w μ * f μ = 0 := by
  refine sum_odd_eq_zero _ ?_ _ _ hw hf
  intro μ hμ
  simp only [mem_filter] at hμ ⊢
  exact ⟨hS μ hμ.1, by simpa [and_comm] using hμ.2⟩

/-- **Where one wall breaks `ω`.** Behind the boson's wall (`ℓ(λ) ≤ N`), the weighted sum of an
`ω`-odd statistic is carried exactly by the shapes that cross the fermion's wall
(`ℓ(λ) ≤ N < λ₁`); the box contributes nothing. -/
theorem sum_bosonWall_odd (S : Finset YoungDiagram) (hS : ∀ μ ∈ S, μ.transpose ∈ S)
    (N : ℕ) (w f : YoungDiagram → R) (hw : OmegaEven w) (hf : OmegaOdd f) :
    ∑ μ ∈ S with numRows μ ≤ N, w μ * f μ =
      ∑ μ ∈ S with numRows μ ≤ N ∧ N < firstRow μ, w μ * f μ := by
  have hbox := sum_box_odd_eq_zero S hS N w f hw hf
  rw [← sum_filter_add_sum_filter_not _ (fun μ => firstRow μ ≤ N)]
  simp only [filter_filter, not_le] at hbox ⊢
  rw [hbox, zero_add]

omit [IsDomain R] [CharZero R] in
/-- The same bias, seen from the other wall: behind the fermion's wall the sign flips. -/
theorem sum_fermionWall_odd (S : Finset YoungDiagram) (hS : ∀ μ ∈ S, μ.transpose ∈ S)
    (N : ℕ) (w f : YoungDiagram → R) (hw : OmegaEven w) (hf : OmegaOdd f) :
    ∑ μ ∈ S with firstRow μ ≤ N, w μ * f μ =
      -∑ μ ∈ S with numRows μ ≤ N, w μ * f μ := by
  rw [← sum_bosonWall_transpose S hS N w f hw, ← sum_neg_distrib]
  refine sum_congr rfl fun μ _ => ?_
  rw [hf, mul_neg]

end CharZero

end RMT.Edges
