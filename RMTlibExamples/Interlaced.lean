import RMTlib.Tableaux.Interlaced
import RMTlibExamples.Growth

/-!
# Checks: RSK for ℕ-matrices, and the reading-word statement

* `rskTwoLine` (growth diagrams + standardization) agrees with row insertion on every ℕ-matrix
  of size `2 × 3` with entries `≤ 2` and `3 × 3` with entries `≤ 1`;
* `ReadingWord` holds on all matrices of weight `ν` for the listed `(k, n, ν)`;
* the number of interlaced matrices equals the number of semistandard tableaux (`dim ∇(ν)`).
-/

namespace RMT.Weyl.Examples

open RMT.Growth RMT.Growth.Examples

/-- Row insertion on a two-line array (`ins` from `RMTlibExamples.Growth`). -/
def insertionTwoLine (pairs : TwoLine) : List (List Nat) × List (List Nat) :=
  pairs.foldl (fun PQ tb => ins PQ.1 PQ.2 tb.2 tb.1) ([], [])

/-- All `r × c` matrices with entries `≤ b`, as lists of rows. -/
def allMatrices (r c b : Nat) : List (List (List Nat)) :=
  let rows := (List.range (r * c)).foldr (fun _ acc => (List.range (b + 1)).flatMap fun x => acc.map (x :: ·)) [[]]
  rows.map fun xs => (List.range r).map fun i => (xs.drop (i * c)).take c

#guard (allMatrices 2 3 2).all fun m => rskTwoLine (twoLineOfRows m) == insertionTwoLine (twoLineOfRows m)
#guard (allMatrices 3 3 1).all fun m => rskTwoLine (twoLineOfRows m) == insertionTwoLine (twoLineOfRows m)

-- The reading-word statement, by enumeration (k, n, ν).
#guard readingWordCheck 2 2 [2, 1]
#guard readingWordCheck 3 3 [3, 2, 1]
#guard readingWordCheck 4 3 [3, 2, 2]
#guard readingWordCheck 3 2 [3, 3]
#guard readingWordCheck 3 3 [2, 2, 2]

-- |ssIdx k n ν| = number of SSYT of shape ν with entries ≤ k (= dim ∇(ν)).
#guard numInterlaced 3 3 [3, 2, 1] == 8
#guard numInterlaced 4 3 [3, 2, 2] == 36
#guard numInterlaced 3 2 [3, 3] == 10

end RMT.Weyl.Examples
