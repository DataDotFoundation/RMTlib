import MeaningLib.Frame
import RMTlib.Symmetric.WeightedCauchy
import RMTlib.BDTW.PatternA

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

/-- Folding lemma: RMTlib writes the archimedean content anonymously, `fun z => N + z`. -/
theorem archContent_fold (N : R) : archContent N = fun z : ℤ => N + (z : R) := rfl

/-- Folding lemma over `ℤ`, where no cast is written: `fun z => N + z`. -/
theorem archContent_fold_int (N : ℤ) : archContent N = fun z : ℤ => N + z := by
  funext z
  simp [archContent]

/-- Folding lemma for the finite place: a constant content function `fun _ => T`. It matches every
constant function `ℤ → R`; on RMTlib this adds 4 reads, all statements about constant content
(RMTlib#7). -/
theorem finContent_fold (T : R) : finContent T = fun _ : ℤ => T := rfl

/-- **The shapes seen at `∞`** (`archSupport`, the wall): at most `N` rows, i.e. `(N, 0) ∉ μ`. -/
def archSupport (N : ℕ) : Set YoungDiagram := {μ | (N, 0) ∉ μ}

/-- **The shapes seen at a finite place** (`finSupport`): all of them, no wall. The rank is not
used; it is kept so that `finSupport` has the type of `archSupport` and the support moves of both
rules (`∞ ↦ finite`, `finite ↦ ∞`) are well typed without an adapter. -/
@[nolint unusedArguments]
def finSupport (_N : ℕ) : Set YoungDiagram := Set.univ

/-- **The wall, in role vocabulary**: the archimedean content product is non-zero exactly on the
archimedean support. Its `∞ ↦ finite` twin (`finContent`, `finSupport`) holds for `N ≠ 0`
(`contentProd_finContent_ne_zero_iff`); at `N = 0` the twin fails off the empty shape. -/
theorem contentProd_archContent_ne_zero_iff (N : ℕ) (μ : YoungDiagram) :
    RMT.Symmetric.contentProd (archContent (N : ℤ)) μ ≠ 0 ↔ μ ∈ archSupport N := by
  rw [archContent_fold_int, Ne, RMT.Symmetric.contentProd_nat_add_eq_zero_iff]
  rfl

/-- At a finite place there is no wall: for `T ≠ 0` the content product never vanishes. -/
theorem contentProd_finContent_ne_zero_iff {N : ℕ} (hN : N ≠ 0) (μ : YoungDiagram) :
    RMT.Symmetric.contentProd (finContent (N : ℤ)) μ ≠ 0 ↔ μ ∈ finSupport N := by
  rw [show finContent (N : ℤ) = fun _ : ℤ => (N : ℤ) from rfl, RMT.Symmetric.contentProd_const]
  simp [finSupport, hN]

/-- RMTlib's binding of the places frame. The folding lemmas let the report read statements that
never name `archContent` (MeaningLib#2). -/
def placesBinding : MeaningLib.Frame.Binding where
  frame := MeaningLib.Frame.places
  assign := [("archContent", ``archContent), ("finContent", ``finContent),
    ("archSupport", ``archSupport), ("finSupport", ``finSupport),
    ("archPotential", ``RMT.BDTW.rhoInf), ("finPotential", ``RMT.BDTW.rhoFin)]
  adapters := [(("archPotential", "finPotential"), ``RMT.BDTW.infToFin),
    (("finPotential", "archPotential"), ``RMT.BDTW.finToInf)]
  folds := [``archContent_fold, ``archContent_fold_int, ``finContent_fold]

/-- At a finite place the content product counts boxes. -/
theorem contentProd_finContent (T : R) (μ : YoungDiagram) :
    RMT.Symmetric.contentProd (finContent T) μ = T ^ μ.cells.card :=
  RMT.Symmetric.contentProd_const T μ

end RMT.Frames
