import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# `ω`-covariant families of statistics on Young diagrams

`ω` is transposition of shapes, `λ ↦ λ′`. Many statistics of a diagram are not invariant under it,
but change in a controlled way: transposing the shape is the same as changing a parameter, and then
correcting the value. For instance, conjugation negates contents, so for content products

  `contentProd f λ′ = contentProd (f ∘ neg) λ`,

and the hook-content product `∏ (N + c)` turns into `(−1)^{|λ|} ∏ (−N + c)`: the `N ↦ −N` swap of
boson and fermion statistics.

`OmegaCovariant F` packages this for a family `F : P → YoungDiagram → R`:

* an involution `twin` of the parameters (`f ↦ f ∘ neg`, `N ↦ −N`, `z ↦ −1 − z`, …);
* a correction `out μ : R → R` of the values (the identity, a sign `(−1)^{|μ|}`, negation, `¬`, …),
  allowed to depend on the shape, subject to `out μ′ ∘ out μ = id`, which is what `ω² = 1` forces;
* the law `F p μ′ = out μ (F (twin p) μ)` (`map_transpose`).

It replaces the tag `@[conj_symmetric]` of the earlier combined repository, which only required
that a lemma named `*_transpose` exist. Here the twin is data: its parameter map and its value map
can be read off, compared and composed, and a tool can list the instances by type.

`ω` is self-twinned: the twin of an `OmegaCovariant` structure is again one, with the same `twin`
and `out` (`map_transpose_twin`, `eq_out_transpose`). No other twin is recorded.

## Main definitions

* `RMT.Symmetric.OmegaCovariant`: the structure.
* `OmegaCovariant.invariant`, `OmegaCovariant.tautological`: the two trivial instances (an
  `ω`-invariant statistic, and the shape itself).
* `OmegaCovariant.comp`: post-composition with a map that intertwines the value corrections.
* `OmegaCovariant.pair`: two covariant families side by side.
* `OmegaCovariant.reindex`: restriction to a subfamily of parameters stable under the twin, up to a
  new value correction.
* `OmegaCovariant.congr`: transport along a pointwise equality of families.

The instances for content products, the hook-content product, the Casimir eigenvalue and Maya
occupation are in `RMTlib.Symmetric.OmegaCovariantInstances`.
-/

namespace RMT.Symmetric

/-- **An `ω`-covariant family of statistics on Young diagrams**: transposing the shape is the same
as replacing the parameter `p` by `twin p` and correcting the value by `out μ`,
`F p μ′ = out μ (F (twin p) μ)`. Both `twin` and the correction square to the identity, as `ω`
does. -/
structure OmegaCovariant {P R : Type*} (F : P → YoungDiagram → R) where
  /-- The action of `ω` on the parameters. -/
  twin : P → P
  /-- `ω` is an involution on the parameters. -/
  twin_involutive : Function.Involutive twin
  /-- The correction of the value at the shape `μ`. -/
  out : YoungDiagram → R → R
  /-- The corrections at `μ` and at `μ′` undo each other. -/
  out_transpose_out : ∀ μ r, out μ.transpose (out μ r) = r
  /-- **The `ω` law**: `F p μ′ = out μ (F (twin p) μ)`. -/
  map_transpose : ∀ p μ, F p μ.transpose = out μ (F (twin p) μ)

namespace OmegaCovariant

variable {P Q R S : Type*} {F : P → YoungDiagram → R} {G : Q → YoungDiagram → S}

/-- The `ω` law read from the twin side: `F (twin p) μ′ = out μ (F p μ)`. -/
theorem map_transpose_twin (h : OmegaCovariant F) (p : P) (μ : YoungDiagram) :
    F (h.twin p) μ.transpose = h.out μ (F p μ) := by
  rw [h.map_transpose, h.twin_involutive p]

/-- The `ω` law solved for the untransposed value: `F p μ = out μ′ (F (twin p) μ′)`. -/
theorem eq_out_transpose (h : OmegaCovariant F) (p : P) (μ : YoungDiagram) :
    F p μ = h.out μ.transpose (F (h.twin p) μ.transpose) := by
  rw [h.map_transpose_twin, h.out_transpose_out]

/-- The correction at `μ` is injective (`out μ′` is a left inverse). -/
theorem out_injective (h : OmegaCovariant F) (μ : YoungDiagram) : Function.Injective (h.out μ) :=
  Function.LeftInverse.injective (h.out_transpose_out μ)

/-- Two parameters with the same twin are equal. -/
theorem twin_injective (h : OmegaCovariant F) : Function.Injective h.twin :=
  h.twin_involutive.injective

/-- **An `ω`-invariant statistic**: trivial twin, trivial correction. -/
def invariant (hF : ∀ p μ, F p μ.transpose = F p μ) : OmegaCovariant F where
  twin := id
  twin_involutive _ := rfl
  out _ r := r
  out_transpose_out _ _ := rfl
  map_transpose := hF

/-- **The shape itself**: the parameter is trivial and all of `ω` sits in the correction,
`out μ ν = ν′`. -/
def tautological : OmegaCovariant (fun (_ : Unit) (μ : YoungDiagram) => μ) where
  twin := id
  twin_involutive _ := rfl
  out _ ν := ν.transpose
  out_transpose_out _ ν := YoungDiagram.transpose_transpose ν
  map_transpose _ _ := rfl

/-- **Post-composition**: if `g` intertwines the correction of `F` with a correction `out'` that
squares to the identity, then `g ∘ F` is covariant with the same twin. -/
def comp (h : OmegaCovariant F) (g : R → S) (out' : YoungDiagram → S → S)
    (hout' : ∀ μ s, out' μ.transpose (out' μ s) = s)
    (hg : ∀ μ r, g (h.out μ r) = out' μ (g r)) :
    OmegaCovariant (fun p μ => g (F p μ)) where
  twin := h.twin
  twin_involutive := h.twin_involutive
  out := out'
  out_transpose_out := hout'
  map_transpose p μ := by
    rw [h.map_transpose, hg]

/-- **Two families side by side**: parameters and values in products, twins and corrections
componentwise. -/
def pair (h : OmegaCovariant F) (k : OmegaCovariant G) :
    OmegaCovariant (fun (pq : P × Q) μ => (F pq.1 μ, G pq.2 μ)) where
  twin pq := (h.twin pq.1, k.twin pq.2)
  twin_involutive pq := by
    simp only [h.twin_involutive pq.1, k.twin_involutive pq.2]
  out μ rs := (h.out μ rs.1, k.out μ rs.2)
  out_transpose_out μ rs := by
    simp only [h.out_transpose_out, k.out_transpose_out]
  map_transpose pq μ := by
    simp only [h.map_transpose, k.map_transpose]

/-- **Restriction to a subfamily**: a family of parameters `ι : Q → P`, an involution `τ` of `Q`
and a new correction `out'`, such that the twin of `ι q` gives, after correction, the value at
`ι (τ q)` corrected by `out'`. This is how a single `ω` law (for instance that of content
products) yields the laws of its specialisations. -/
def reindex (h : OmegaCovariant F) (ι : Q → P) (τ : Q → Q) (hτ : Function.Involutive τ)
    (out' : YoungDiagram → R → R) (hout' : ∀ μ r, out' μ.transpose (out' μ r) = r)
    (hι : ∀ q μ, h.out μ (F (h.twin (ι q)) μ) = out' μ (F (ι (τ q)) μ)) :
    OmegaCovariant (fun q μ => F (ι q) μ) where
  twin := τ
  twin_involutive := hτ
  out := out'
  out_transpose_out := hout'
  map_transpose q μ := (h.map_transpose (ι q) μ).trans (hι q μ)

/-- **Transport along a pointwise equality** of families, with the same twin and correction. -/
def congr (h : OmegaCovariant F) {F' : P → YoungDiagram → R} (hF : ∀ p μ, F p μ = F' p μ) :
    OmegaCovariant F' where
  twin := h.twin
  twin_involutive := h.twin_involutive
  out := h.out
  out_transpose_out := h.out_transpose_out
  map_transpose p μ := by
    rw [← hF, ← hF, h.map_transpose]

end OmegaCovariant

end RMT.Symmetric
