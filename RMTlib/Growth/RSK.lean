/-!
# RSK via Fomin growth diagrams, as a two-variable recursor

No Mathlib. A shape is a weakly decreasing `List Nat` of row lengths.
The whole construction is:

* one *local rule* on a unit square (the combinatorial content of `DU - UD = I`),
* an outer `Nat` recursion over the rows of the permutation matrix,
* an inner `List` recursion across the columns.

Both recursions are structural, so the elaborator compiles them to `Nat.rec` / `List.rec`
(through `brecOn`). `rowRec` below writes the outer one as a literal `Nat.rec`.

## Changes on inclusion in RMTlib
The construction is unchanged. It now lives in `namespace RMT.Growth`, `Shape` and `rowRec_eq`
have docstrings (RMTlib builds with `linter.missingDocs`), and the `#eval` examples are now
`#guard` checks in `RMTlibExamples/Growth.lean`, together with a comparison against Schensted
row insertion on every permutation of size at most 6.
-/

namespace RMT.Growth

/-- A Young diagram, as its weakly decreasing list of row lengths. -/
abbrev Shape := List Nat

namespace Shape

/-- Union of Young diagrams = componentwise max of row lengths. -/
def sup : Shape → Shape → Shape
  | [], l => l
  | l, [] => l
  | a :: xs, b :: ys => max a b :: sup xs ys

/-- Add a box at the end of row `i` (0-indexed); `i = length` opens a new row. -/
def addRow : Shape → Nat → Shape
  | [], _ => [1]
  | a :: xs, 0 => (a + 1) :: xs
  | a :: xs, i + 1 => a :: addRow xs i

/-- If `μ = ρ + one box`, the row containing that box. -/
def diffRow : Shape → Shape → Nat
  | a :: xs, b :: ys => if a = b then diffRow xs ys + 1 else 0
  | _, _ => 0

end Shape

open Shape

/-- Fomin's local rule. `ρ` is the corner opposite the new shape; `μ, ν` are its two
neighbours; `x` says whether the square holds a 1 of the permutation matrix.
1. `μ ≠ ν`        ⇒ `μ ∪ ν`
2. `μ = ν = ρ`    ⇒ `ρ`, or `ρ` plus a box in row 0 if `x`
3. `μ = ν ≠ ρ`    ⇒ `μ` plus a box one row below where `μ` grew from `ρ`  -/
def localRule (ρ μ ν : Shape) (x : Bool) : Shape :=
  if μ ≠ ν then sup μ ν
  else if μ = ρ then (if x then addRow ρ 0 else ρ)
  else addRow μ (diffRow μ ρ + 1)

/-- Inner recursion (on `List`): sweep one row of squares left to right.
`prev` = shapes on the lower edge, `left` = shape already computed at the left,
`wi` = column of the 1 in this row. -/
def nextRow (wi : Nat) : List Shape → Shape → Nat → List Shape
  | ρ :: tl@(σ :: _), left, j =>
      let cur := localRule ρ σ left (wi == j)
      cur :: nextRow wi tl cur (j + 1)
  | _, _, _ => []

/-- Outer recursion (on `Nat`): row `i` of shapes, for `w` a permutation of
`0, …, n-1` given as a list of values. -/
def row (w : List Nat) : Nat → List Shape
  | 0 => List.replicate (w.length + 1) []
  | i + 1 => [] :: nextRow (w.getD i 0) (row w i) [] 0

/-- The same outer recursion as a literal `Nat.rec`. -/
noncomputable def rowRec (w : List Nat) (i : Nat) : List Shape :=
  Nat.rec (motive := fun _ => List Shape)
    (List.replicate (w.length + 1) [])
    (fun i prev => [] :: nextRow (w.getD i 0) prev [] 0) i

/-- `rowRec` (the literal `Nat.rec`) agrees with the structural `row`. -/
theorem rowRec_eq (w : List Nat) : ∀ i, rowRec w i = row w i
  | 0 => rfl
  | i + 1 => by
    show [] :: nextRow (w.getD i 0) (rowRec w i) [] 0 = row w (i + 1)
    rw [rowRec_eq w i]; rfl

/-! ## Reading off the tableaux -/

/-- Append value `v` to row `i` of a tableau. -/
def tabAdd : List (List Nat) → Nat → Nat → List (List Nat)
  | [], _, v => [[v]]
  | r :: rs, 0, v => (r ++ [v]) :: rs
  | r :: rs, i + 1, v => r :: tabAdd rs i v

/-- A saturated chain `∅ ⋖ λ₁ ⋖ ⋯ ⋖ λₙ` in Young's lattice ↦ standard Young tableau.
(A term of the `Growth` inductive family, flattened.) -/
def chainToTableau : List Shape → Nat → List (List Nat) → List (List Nat)
  | a :: tl@(b :: _), k, T => chainToTableau tl (k + 1) (tabAdd T (diffRow b a) (k + 1))
  | _, _, T => T

/-- RSK: `(P, Q)` = chains along the top and right edges of the growth diagram. -/
def rsk (w : List Nat) : List (List Nat) × List (List Nat) :=
  let n := w.length
  let rows := (List.range (n + 1)).map (row w)
  let top := rows.getLastD []
  let right := rows.map (·.getLastD [])
  (chainToTableau top 0 [], chainToTableau right 0 [])

end RMT.Growth
