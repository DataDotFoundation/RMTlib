import MeaningLib.Frame
import RMTlib.Symmetric.WeightedCauchy

/-!
# RMTlib's binding of the places frame

The places frame (`MeaningLib.Frame.places`, our reading of Scholze's programme, not his claim)
has two roles in content form: the content function at `∞` and at a finite place. RMTlib plays
them with

* `archContent N : ℤ → R`, `c ↦ N + c` (the hook-content weight `∏ (N + c)` is
  `contentProd (archContent N)`);
* `finContent T : ℤ → R`, `c ↦ T` (`contentProd (finContent T) λ = T^{|λ|}`).

Both have the same type, so the twin rule `archContent ↦ finContent` turns a statement about the
archimedean content into a well-typed statement about the finite one. Run the report with
`#frame_report RMT.Frames.placesBinding in <namespace>`.
-/

namespace RMT.Frames

variable {R : Type*} [CommRing R]

/-- The content function at `∞`: `c ↦ N + c`. -/
def archContent (N : R) : ℤ → R := fun c => N + c

/-- The content function at a finite place: `c ↦ T`. The ring structure is not used, but is kept
as an argument so that `finContent` has the same type as `archContent` (the twin rule substitutes
one constant for the other). -/
@[nolint unusedArguments]
def finContent {R : Type*} [CommRing R] (T : R) : ℤ → R := fun _ => T

/-- RMTlib's binding of the places frame. -/
def placesBinding : MeaningLib.Frame.Binding where
  frame := MeaningLib.Frame.places
  assign := [("archContent", ``archContent), ("finContent", ``finContent)]

/-- At a finite place the content product counts boxes. -/
theorem contentProd_finContent (T : R) (μ : YoungDiagram) :
    RMT.Symmetric.contentProd (finContent T) μ = T ^ μ.cells.card :=
  RMT.Symmetric.contentProd_const T μ

end RMT.Frames
