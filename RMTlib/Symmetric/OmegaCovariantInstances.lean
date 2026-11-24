import RMTlib.Symmetric.OmegaCovariant
import RMTlib.Symmetric.WeightedCauchy
import RMTlib.Tableaux.MultisetHook.Maya

/-!
# Instances of `OmegaCovariant`

The `ω` laws of the library, as data (`RMT.Symmetric.OmegaCovariant`):

| family | `twin` | `out μ` | from |
|---|---|---|---|
| `contentProd f μ` | `f ↦ f ∘ neg` | `id` | `contentProd_transpose` |
| `∏_{□ ∈ μ} (N + c(□))` | `N ↦ −N` | `(−1)^{|μ|} ·` | `reindex` of the line above |
| `Σ_{□ ∈ μ} (N + 2c(□))` (Casimir) | `N ↦ −N` | `−` | `reindex` of the first line, additively |
| `Occ μ z` (Maya occupation) | `z ↦ −1 − z` | `¬` | `MultisetHook.occ_transpose` |

The second and third rows are not proved separately: both are specialisations of the first, so
one argument (transposition swaps the coordinates of a cell, and negates its content) gives all
three. The Casimir row uses content products in `Multiplicative R`, where products are sums.
-/

namespace RMT.Symmetric

open Finset

section ContentProd

variable (R : Type*) [CommMonoid R]

/-- **Content products are `ω`-covariant**: `contentProd f μ′ = contentProd (f ∘ neg) μ`, with no
correction of the value. -/
def omegaContentProd : OmegaCovariant (contentProd (R := R)) where
  twin f z := f (-z)
  twin_involutive f := by
    funext z
    simp
  out _ r := r
  out_transpose_out _ _ := rfl
  map_transpose f μ := contentProd_transpose f μ

end ContentProd

/-- The sign `(−1)^{|μ|}` is unchanged by transposition. -/
theorem neg_one_pow_card_transpose {R : Type*} [CommRing R] (μ : YoungDiagram) :
    ((-1 : R) ^ μ.transpose.cells.card) = (-1) ^ μ.cells.card := by
  have h := contentProd_transpose (fun _ : ℤ => (-1 : R)) μ
  rwa [contentProd_const, contentProd_const] at h

section HookContent

variable (R : Type*) [CommRing R]

/-- **The hook-content product turns `N` into `−N`**:
`∏_{□ ∈ μ′} (N + c(□)) = (−1)^{|μ|} ∏_{□ ∈ μ} (−N + c(□))`. The boson–fermion swap `N ↦ −N`, as
a specialisation of `omegaContentProd`. -/
def omegaHookContent :
    OmegaCovariant (fun (N : R) (μ : YoungDiagram) => contentProd (fun z : ℤ => N + z) μ) :=
  (omegaContentProd R).reindex (fun N z => N + z) Neg.neg neg_involutive
    (fun μ r => (-1) ^ μ.cells.card * r)
    (fun μ r => by
      rw [neg_one_pow_card_transpose, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow,
        one_mul])
    (fun N μ => by
      simp only [omegaContentProd]
      rw [← contentProd_const, ← contentProd_mul]
      congr 1
      funext z
      push_cast
      ring)

/-- The Casimir eigenvalue `Σ_{□ ∈ μ} (N + 2c(□))`, as a content product in `Multiplicative R`. -/
theorem sum_content_eq_toAdd_contentProd (N : R) (μ : YoungDiagram) :
    ∑ c ∈ μ.cells, (N + 2 * (content c : R))
      = (contentProd (fun z : ℤ => Multiplicative.ofAdd (N + 2 * (z : R))) μ).toAdd := by
  simp [contentProd, toAdd_prod]

/-- **The Casimir eigenvalue turns `N` into `−N`, up to sign**:
`Σ_{□ ∈ μ′} (N + 2c(□)) = −Σ_{□ ∈ μ} (−N + 2c(□))`. The additive twin of `omegaHookContent`, and
a specialisation of the same `omegaContentProd`, taken in `Multiplicative R`. -/
def omegaCasimir :
    OmegaCovariant (fun (N : R) (μ : YoungDiagram) => ∑ c ∈ μ.cells, (N + 2 * (content c : R))) :=
  (((omegaContentProd (Multiplicative R)).comp Multiplicative.toAdd (fun _ r => r)
      (fun _ _ => rfl) (fun _ _ => rfl)).reindex
    (fun N z => Multiplicative.ofAdd (N + 2 * (z : R))) Neg.neg neg_involutive
    (fun _ r => -r) (fun _ r => neg_neg r)
    (fun N μ => by
      simp only [omegaContentProd, OmegaCovariant.comp, contentProd, toAdd_prod, toAdd_ofAdd,
        ← sum_neg_distrib]
      refine sum_congr rfl fun c _ => ?_
      push_cast
      ring)).congr
    (fun N μ => (sum_content_eq_toAdd_contentProd R N μ).symm)

/-- The twins are the expected ones, by definition. -/
example (R : Type*) [CommRing R] (N : R) :
    (omegaCasimir R).twin N = -N ∧ (omegaHookContent R).twin N = -N := ⟨rfl, rfl⟩

end HookContent

section Maya

open MultisetHook

/-- **Maya occupation**: the site `z` of `μ′` is occupied exactly when the site `−1 − z` of `μ` is
empty. `ω` exchanges particles and holes. -/
def omegaOcc : OmegaCovariant (fun (z : ℤ) (μ : YoungDiagram) => Occ μ z) where
  twin z := -1 - z
  twin_involutive z := by
    simp only
    ring
  out _ r := ¬ r
  out_transpose_out _ _ := propext not_not
  map_transpose z μ := propext (occ_transpose μ z)

end Maya

end RMT.Symmetric
