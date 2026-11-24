/-!
# Tableaux and the conditions shared by the bumping proofs

This file opens `RMTlib.RSK`: three proofs that RSK is invertible, each with a different
recursion scheme, and each proof a recursion of the same kind as the function it is about.

* `RMTlib.RSK.Nested`: row bumping as structural recursion nested two levels deep (along a
  row, inside a recursion down the rows).
* `RMTlib.RSK.Zipper`: row bumping as one tail recursion over a zipper in each direction,
  well-founded on a lexicographic measure; insertion and uninsertion mirror each other.
* `RMTlib.RSK.Growth`: Fomin growth diagrams as one recursion over the grid in each direction;
  all the invertibility sits in one square (`bwd_fwd`).
* `RMTlib.RSK.Semistandard`: uninsertion preserves semistandardness, and the two bumping
  versions compute the same functions.

All four are Mathlib-free. `RMTlibExamples/RSK.lean` checks that the existing
`RMT.Growth.rsk` (`RMTlib.Growth.RSK`) agrees with the bumping RSK of `RMT.RSK.Nested` on every
permutation of size at most 6.

## Changes on inclusion in RMTlib
The proofs come from the `RSK/` package of `pdehaye/MMT`. They now live in `namespace RMT.RSK`,
and one core lemma was renamed for Lean 4.33 (`List.getElem_inj` for `List.Nodup.getElem_inj`).

A tableau is a list of rows, each a list of natural numbers. The bumping proofs
(`RSK.Nested`, `RSK.Zipper`) use only two shape facts about tableaux:

* every row is weakly increasing and nonempty (`Good`);
* the first column is strictly increasing (`ColStrict`), stated as `Adj`: some entry of
  each row is smaller than every entry of the row below.

Every semistandard Young tableau satisfies both.

`Valid un t is` says the recording data `is` can be peeled off `t` one box at a time
using the uninsertion function `un`: at every stage the tableau satisfies the two
conditions above and the index is a corner. Both bumping proofs state their
"inverse after forward" theorem with the same `Valid`, applied to their own `un`.
-/

namespace RMT.RSK

/-- A row of a tableau. -/
abbrev Row := List Nat

/-- A tableau, as its list of rows from top to bottom. -/
abbrev Tab := List Row

/-- A row is weakly increasing. -/
def Sorted (r : Row) : Prop := r.Pairwise (· ≤ ·)

/-- Every row is weakly increasing and nonempty. -/
def Good (t : Tab) : Prop := ∀ r ∈ t, Sorted r ∧ r ≠ []

/-- Some entry of `a` is smaller than every entry of `b`. For sorted rows this says
`a.head < b.head`. -/
def Adj (a b : Row) : Prop := ∃ w ∈ a, ∀ v ∈ b, w < v

/-- The first column is strictly increasing. -/
def ColStrict (t : Tab) : Prop := ∀ j (h : j + 1 < t.length), Adj t[j] t[j+1]

/-- Row `i` exists and its last box is a corner: the row below, if any, is shorter. -/
def Corner (i : Nat) (t : Tab) : Prop :=
  ∃ hi : i < t.length, ∀ h : i + 1 < t.length, t[i+1].length < t[i].length

/-- The recording data `is` can be peeled off `t` by `un`, one corner at a time, down to
the empty tableau. -/
def Valid (un : Nat → Tab → Tab × Nat) : Tab → List Nat → Prop
  | t, [] => t = []
  | t, i :: is => Good t ∧ ColStrict t ∧ Corner i t ∧ Valid un (un i t).1 is

theorem Good.tail {r : Row} {rs : Tab} (h : Good (r :: rs)) : Good rs :=
  fun r' h' => h r' (List.mem_cons_of_mem _ h')

theorem ColStrict.tail {r : Row} {rs : Tab} (h : ColStrict (r :: rs)) : ColStrict rs :=
  fun j hj => h (j + 1) (by simp; omega)

theorem Corner.tail {i : Nat} {r : Row} {rs : Tab} (h : Corner (i + 1) (r :: rs)) :
    Corner i rs := by
  obtain ⟨hi, hc⟩ := h
  exact ⟨by simp at hi; omega, fun h' => hc (by simp; omega)⟩

end RMT.RSK
