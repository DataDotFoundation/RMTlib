import Mathlib
import RMTlib.Growth.Matrix

/-!
# The index set of the RH formalisation's basis of `∇(ν)`, and RSK

The claimed RH formalisation (`pdehaye/riemann-hypothesis-lean`) gives a basis of the dual Weyl
module `∇(ν)` of `GL_k` by bideterminants (`Formalism.GradedWeylDivisibility.SSBasis`), indexed by
`ssIdx k n ν`: the matrices `m : Fin k × Fin n →₀ ℕ` with column sums `ν` that are `Interlaced`
(`StatementC`), and whose column-lex leading monomial is `m` itself. This file copies those
definitions for functions `Fin k × Fin n → ℕ` (the bridge package proves they agree with the
originals) and relates them to RSK.

Read `m` as a filling: row `t` contains `a + 1` exactly `m (a, t)` times (`tableauOf`). Insert
the rows of that filling from the bottom up, recording row `t` with label `n − t`
(`readingPairs`). The statement `ReadingWord` says:

* `m` is interlaced exactly when the recording tableau is one fixed tableau `Qnu ν`;
* then the insertion tableau is the filling itself.

In growth-diagram terms (`RMT.Growth`): the basis of `∇(ν)` consists of the solutions of the
characteristic (Goursat) problem whose data on one null boundary is fixed to `Qnu ν`, and the
free data on the other boundary is the semistandard tableau. `ReadingWord` is checked on small
cases in `RMTlibExamples/Interlaced.lean` and proved in `RMTlib.Tableaux.ReadingWord`
(`RMT.Weyl.readingWord_holds`).
-/

open Finset RMT.Growth

namespace RMT.Weyl

/-- Copy of `Formalism.GradedWeylDivisibility.InterlacedAt 0 l j` (RH formalisation, `StatementC`). -/
def InterlacedAt {k n : ℕ} (l j : Fin n) (m : Fin k × Fin n → ℕ) : Prop :=
  ∀ a : Fin k, (∑ b : Fin k with b ≤ a, m (b, j)) ≤ ∑ b : Fin k with b < a, m (b, l)

/-- Copy of `Formalism.GradedWeylDivisibility.Interlaced` (RH formalisation, `StatementC`):
consecutive columns interlace. -/
def Interlaced {k n : ℕ} (m : Fin k × Fin n → ℕ) : Prop :=
  ∀ l j : Fin n, j.val = l.val + 1 → InterlacedAt l j m

instance {k n : ℕ} (l j : Fin n) (m : Fin k × Fin n → ℕ) : Decidable (InterlacedAt l j m) := by
  unfold InterlacedAt; infer_instance

instance {k n : ℕ} (m : Fin k × Fin n → ℕ) : Decidable (Interlaced m) := by
  unfold Interlaced; infer_instance

/-- Column `t` of `m` sums to `ν t` (the weight condition of `ssIdx`). -/
def ColSums {k n : ℕ} (m : Fin k × Fin n → ℕ) (ν : Fin n → ℕ) : Prop :=
  ∀ t : Fin n, ∑ a : Fin k, m (a, t) = ν t

instance {k n : ℕ} (m : Fin k × Fin n → ℕ) (ν : Fin n → ℕ) : Decidable (ColSums m ν) := by
  unfold ColSums; infer_instance

/-- The filling encoded by `m`: row `t` lists `a + 1` with multiplicity `m (a, t)`. -/
def tableauOf {k n : ℕ} (m : Fin k × Fin n → ℕ) : List (List ℕ) :=
  ((List.finRange n).map fun t =>
    (List.finRange k).flatMap fun a => List.replicate (m (a, t)) (a.val + 1)).filter (· ≠ [])

/-- The rows of the filling inserted from the bottom up: row `t` contributes the pairs
`(n − t, a + 1)`, `m (a, t)` times each, so the array is in lexicographic order. -/
def readingPairs {k n : ℕ} (m : Fin k × Fin n → ℕ) : TwoLine :=
  (List.finRange n).reverse.flatMap fun t =>
    (List.finRange k).flatMap fun a => List.replicate (m (a, t)) (n - t.val, a.val + 1)

/-- The superstandard filling of shape `ν`: row `t` filled with `t + 1`. -/
def superstandard {k n : ℕ} (ν : Fin n → ℕ) : Fin k × Fin n → ℕ :=
  fun p => if p.1.val = p.2.val then ν p.2 else 0

/-- The fixed recording tableau: that of the superstandard filling. -/
def Qnu (k : ℕ) {n : ℕ} (ν : Fin n → ℕ) : List (List ℕ) :=
  (rskTwoLine (readingPairs (superstandard (k := k) ν))).2

/-- **The reading-word statement.** For `ν` weakly decreasing with `n ≤ k` and `m` of weight
`ν`: `m` lies in the RH formalisation's index set exactly when the recording tableau of its
reading word is `Qnu k ν`, and then the insertion tableau is the filling of `m`. -/
def ReadingWord : Prop :=
  ∀ (k n : ℕ) (ν : Fin n → ℕ), Antitone ν → n ≤ k → ∀ m : Fin k × Fin n → ℕ, ColSums m ν →
    (Interlaced m ↔ (rskTwoLine (readingPairs m)).2 = Qnu k ν) ∧
    (Interlaced m → (rskTwoLine (readingPairs m)).1 = tableauOf m)

/-! ### Enumeration, for checks -/

/-- All `c : List ℕ` of length `len` with sum `s`. -/
def compositions : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | len + 1, s => (List.range (s + 1)).flatMap fun c => (compositions len (s - c)).map (c :: ·)

/-- All matrices `Fin k × Fin n → ℕ` with column sums `ν` (given as a list). -/
def matricesWithColSums (k n : ℕ) (ν : List ℕ) : List (Fin k × Fin n → ℕ) :=
  let cols := (List.range n).map fun t => compositions k (ν.getD t 0)
  let choices := cols.foldr (fun cs acc => cs.flatMap fun c => acc.map (c :: ·)) [[]]
  choices.map fun ch => fun p => (ch.getD p.2.val []).getD p.1.val 0

/-- `ReadingWord` at one `(k, n, ν)`, as a Boolean, by enumeration. -/
def readingWordCheck (k n : ℕ) (ν : List ℕ) : Bool :=
  let νf : Fin n → ℕ := fun t => ν.getD t.val 0
  let Q := Qnu k νf
  (matricesWithColSums k n ν).all fun m =>
    let PQ := rskTwoLine (readingPairs m)
    (decide (Interlaced m) == (PQ.2 == Q)) && (!decide (Interlaced m) || PQ.1 == tableauOf m)

/-- The number of matrices of weight `ν` that are interlaced. -/
def numInterlaced (k n : ℕ) (ν : List ℕ) : ℕ :=
  ((matricesWithColSums k n ν).filter fun m => decide (Interlaced m)).length

end RMT.Weyl
