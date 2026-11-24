import RMTlib.Growth.RSK
import Mathlib.Data.List.Permutation

/-!
# Checks for RSK via growth diagrams

* the examples from the original `GrowthRSK.lean`, as `#guard`s;
* agreement with Schensted row insertion on every permutation of size `≤ 6`;
* counts of saturated chains in Young's lattice (= standard Young tableaux): the squares give
  `1, 2, 42, 24024`, the numbers `g_k` of `RMTlib.Tableaux.Square`;
* the RSK shape distribution: shape `λ` occurs for exactly `(f^λ)²` permutations.
-/

namespace RMT.Growth.Examples

open RMT.Growth

-- The original examples. w = 3 1 2 (1-indexed). Schensted: P = [[1,2],[3]], Q = [[1,3],[2]].
#guard rsk [2, 0, 1] == ([[1, 2], [3]], [[1, 3], [2]])
#guard rsk [3, 1, 0, 4, 2] == ([[1, 3], [2, 5], [4]], [[1, 4], [2, 5], [3]])
#guard row [1, 3, 0, 2] 4 == [[], [1], [1, 1], [2, 1], [2, 2]]

/-! ## Schensted row insertion, for comparison -/

/-- Insert `x` in a row: replace the leftmost entry larger than `x`, returning the bumped one. -/
def insertRow : List Nat → Nat → List Nat × Option Nat
  | [], x => ([x], none)
  | y :: ys, x =>
    if x < y then (x :: ys, some y)
    else let (r, b) := insertRow ys x; (y :: r, b)

/-- Insert `x` into `P` (bumping down the rows), recording time `t` in `Q`. -/
def ins : List (List Nat) → List (List Nat) → Nat → Nat → List (List Nat) × List (List Nat)
  | [], _, x, t => ([[x]], [[t]])
  | p :: ps, Q, x, t =>
    match insertRow p x with
    | (p', none) => (p' :: ps, Q.modifyHead (· ++ [t]))
    | (p', some y) =>
      let (P', Q') := ins ps Q.tail y t
      (p' :: P', Q.headD [] :: Q')

/-- Classical RSK by row insertion (entries shifted to `1, …, n` as in `rsk`). -/
def schensted (w : List Nat) : List (List Nat) × List (List Nat) :=
  (w.zip (List.range w.length)).foldl (fun PQ xt => ins PQ.1 PQ.2 (xt.1 + 1) (xt.2 + 1)) ([], [])

#guard schensted [3, 1, 0, 4, 2] == ([[1, 3], [2, 5], [4]], [[1, 4], [2, 5], [3]])

-- Growth diagrams and row insertion agree on every permutation of size `≤ 6` (873 in all).
#guard (List.range 7).all fun n => (List.range n).permutations.all fun w => rsk w == schensted w

/-! ## Counting standard Young tableaux by saturated chains -/

/-- Remove the last box of row `i`, dropping a row that becomes empty. -/
def removeBox : Shape → Nat → Shape
  | [], _ => []
  | a :: xs, 0 => if a ≤ 1 then xs else (a - 1) :: xs
  | a :: xs, i + 1 => a :: removeBox xs i

/-- Row `i` ends in a removable corner. -/
def isCorner (s : Shape) (i : Nat) : Bool := s.getD i 0 > s.getD (i + 1) 0

/-- Number of saturated chains `∅ ⋖ ⋯ ⋖ s` in Young's lattice, i.e. of standard Young
tableaux of shape `s` (`fuel` ≥ the number of boxes). -/
def numSYT : Nat → Shape → Nat
  | _, [] => 1
  | 0, _ => 0
  | f + 1, s => ((List.range s.length).filter (isCorner s)).foldl
      (fun acc i => acc + numSYT f (removeBox s i)) 0

#guard (List.range 5).map (fun k => numSYT (k * k) (List.replicate k k)) == [1, 1, 2, 42, 24024]

/-- The RSK shape of `w`. -/
def shapeOf (w : List Nat) : Shape := (rsk w).1.map List.length

-- RSK is a bijection onto pairs of tableaux of the same shape: shape `λ` occurs for exactly
-- `(f^λ)²` permutations. Checked for `n = 5`.
#guard [[5], [4, 1], [3, 2], [3, 1, 1], [2, 2, 1], [2, 1, 1, 1], [1, 1, 1, 1, 1]].all fun s =>
  ((List.range 5).permutations.filter (shapeOf · == s)).length == numSYT 5 s ^ 2

end RMT.Growth.Examples
