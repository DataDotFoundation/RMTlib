import RMTlib.RSK.Semistandard
import RMTlib.RSK.Growth
import RMTlib.Growth.RSK
import RMTlib.RSK.Fold
import RMTlib.RSK.Fuel
import RMTlib.RSK.Mutual
import RMTlib.RSK.GrowthRows

/-!
# Checks for the invertibility proofs of `RMTlib.RSK`

* one word through each of the three versions;
* the nested and zipper bumping versions agree, and both round trips hold, on every word of
  length `≤ 5` over a 4-letter alphabet;
* the proved growth diagram `RMT.RSK.Growth` gives the same P and Q as bumping;
* **link with `RMT.Growth.rsk`**: on every permutation of size `≤ 6`, the existing
  growth-diagram RSK of `RMTlib.Growth.RSK` computes the same (P, Q) as the bumping RSK whose
  invertibility is proved in `RMT.RSK.Nested`.

The nested version is structural recursion, so the kernel evaluates it and its examples are
checked by `decide`. The zipper and growth versions are well-founded recursions, which the kernel
does not unfold usefully, so they are checked by `#guard`.
-/

namespace RMT.RSK.Examples

/-! ## One word through each version -/

example : Nested.rsk [3, 1, 4, 1, 5, 9, 2, 6]
    = ([[1, 1, 3], [2, 4], [5, 9], [6]], [0, 3, 2, 2, 1, 0, 1, 0]) := by decide

example : (let p := Nested.rsk [3, 1, 4, 1, 5, 9, 2, 6]; Nested.unrsk p.1 p.2)
    = [3, 1, 4, 1, 5, 9, 2, 6] := by decide

#guard Zipper.rsk [3, 1, 4, 1, 5, 9, 2, 6]
    = ([[1, 1, 3], [2, 4], [5, 9], [6]], [0, 3, 2, 2, 1, 0, 1, 0])

-- The proved growth diagram takes a permutation of `0, …, n-1` and returns (P, Q), 0-based.
#guard RSK.Growth.rskGrowth [2, 0, 3, 1] = ([[0, 1], [2, 3]], [[0, 2], [1, 3]])
#guard RSK.Growth.unrskGrowth [2, 0, 3, 1] = [2, 0, 3, 1]
#guard RSK.Growth.unrskGrowth [4, 2, 0, 3, 1] = [4, 2, 0, 3, 1]

/-! ## The versions agree -/

/-- All words of length `n` over `{0, …, k-1}`. -/
def words (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (words k n).flatMap fun w => (List.range k).map (· :: w)

/-- All permutations of `{0, …, n-1}`. -/
def perms : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (perms n).flatMap fun p =>
      (List.range (n + 1)).map fun k => p.take k ++ [n] ++ p.drop k

/-- The recording tableau Q built from the row indices returned by the bumping versions
(entries `0, …, n-1`). -/
def qOf (idx : List Nat) : List (List Nat) :=
  (idx.reverse.zipIdx).foldl (fun t (r, k) => RSK.Growth.addAt r k t) []

/-- Bumping RSK of a permutation, inserting left to right, as (P, Q) with 0-based entries. -/
def bumpPQ (w : List Nat) : List (List Nat) × List (List Nat) :=
  let b := Nested.rsk w.reverse
  (b.1, qOf b.2)

/-- Add one to every entry of a tableau. -/
def succTab (t : List (List Nat)) : List (List Nat) := t.map (·.map (· + 1))

-- Nested and zipper bumping compute the same insertion tableau and recording data, and both
-- round trips hold, on all 1,365 words of length at most 5 over a 4-letter alphabet.
#guard ((List.range 6).flatMap (words 4)).all fun w =>
  Nested.rsk w == Zipper.rsk w &&
  Nested.unrsk (Nested.rsk w).1 (Nested.rsk w).2 == w &&
  Zipper.unrsk (Zipper.rsk w).1 (Zipper.rsk w).2 == w

-- The proved growth diagram gives the same P and Q as bumping, and inverse growth recovers the
-- permutation, for all 34 permutations of size at most 4. (`grow` and `back` recompute
-- subproblems, so they take exponential time.)
#guard ((List.range 5).flatMap perms).all fun π =>
  RSK.Growth.rskGrowth π == bumpPQ π && RSK.Growth.unrskGrowth π == π

-- `RMT.Growth.rsk` (entries `1, …, n`) agrees with the bumping RSK of `RMT.RSK.Nested` on all
-- 873 permutations of size at most 6. So `RMT.RSK.Nested.unrsk` inverts it there.
#guard ((List.range 7).flatMap perms).all fun π =>
  let b := bumpPQ π
  RMT.Growth.rsk π == (succTab b.1, succTab b.2)

/-! ## The recursion-scheme landscape: every computable version agrees -/

-- The fold, fuel and mutual-recursion insertions compute the same `(P, recording data)` as
-- nested bumping on all 1,365 words of length at most 5 over a 4-letter alphabet, and the
-- left-to-right fold is bumping of the reversed word.
#guard ((List.range 6).flatMap (words 4)).all fun w =>
  Fold.rsk w == Nested.rsk w && Fold.rskl w == Nested.rsk w.reverse &&
  Fuel.rsk w == Nested.rsk w && Mutual.rsk w == Nested.rsk w

-- Growth diagrams by structural rows give the same P and Q as bumping and invert, on all 873
-- permutations of size at most 6. (Polynomial time, unlike `RSK.Growth.rskGrowth`, which is
-- only checked up to size 4 above.)
#guard ((List.range 7).flatMap perms).all fun π =>
  RSK.GrowthRows.rskRows π == bumpPQ π && RSK.GrowthRows.unrskRows π == π

end RMT.RSK.Examples
