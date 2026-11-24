import RMTlib.Growth.RSK

/-!
# RSK for ℕ-matrices, through standardization

`RMT.Growth.rsk` (Fomin growth diagrams) takes a permutation. An ℕ-matrix, or equivalently
a two-line array of pairs `(top, bottom)` in lexicographic order, is reduced to a permutation by
*standardization*: the bottom entries are replaced by their ranks, ties broken from left to
right, and the times by their positions. RSK commutes with standardization, so running the growth
diagram on the standardized word and then putting the original entries back gives Knuth's RSK.

Mathlib-free, like `RMTlib.Growth.RSK`. The checks against row insertion are in
`RMTlibExamples/Matrix.lean`.
-/

namespace RMT.Growth

/-- A two-line array: pairs `(top, bottom)`, listed in lexicographic order. -/
abbrev TwoLine := List (Nat × Nat)

/-- The standardized word of a list of bottom entries: each entry is replaced by its rank
(from `0`), with equal entries ranked from left to right. -/
def standardize (bs : List Nat) : List Nat :=
  let sorted := (bs.zip (List.range bs.length)).mergeSort
    (fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2))
  (List.range bs.length).map fun i => (sorted.findIdx? (·.2 == i)).getD 0

/-- Knuth's RSK of a two-line array: the growth-diagram `rsk` of the standardized word, with
the standardized values replaced by the bottom entries and the times by the top entries. -/
def rskTwoLine (pairs : TwoLine) : List (List Nat) × List (List Nat) :=
  let tops := pairs.map (·.1)
  let bots := pairs.map (·.2)
  let PQ := rsk (standardize bots)
  let sortedBots := bots.mergeSort (· ≤ ·)
  (PQ.1.map (·.map fun v => sortedBots.getD (v - 1) 0),
   PQ.2.map (·.map fun j => tops.getD (j - 1) 0))

/-- The two-line array of an ℕ-matrix given as a list of rows: the pair `(i+1, j+1)` appears
`m i j` times, in lexicographic order. -/
def twoLineOfRows (m : List (List Nat)) : TwoLine :=
  (m.zip (List.range m.length)).flatMap fun (row, i) =>
    (row.zip (List.range row.length)).flatMap fun (c, j) => List.replicate c (i + 1, j + 1)

end RMT.Growth
