import RMTlib.RSK.Semistandard

/-!
# RSK insertion as a fuel-bounded loop, and as a `partial def`

`Zipper.go` is one tail-recursive loop, well-founded on the lexicographic measure
`(below.length, row.length)`. Here the same loop recurses structurally on an explicit
counter instead: `goF` takes `fuel : Nat`, spends one unit per step, and returns `none` if it
runs out. The insertion `insF` gives it the fuel `bound t`, which is the number of boxes
plus the number of rows plus one, and `ins` reads the result off with a default.

For contrast, `goP` is the same loop as a `partial def`, with no termination argument at
all.

## The recursion scheme and what it costs

* Termination: nothing to prove for `goF`; it is structural on `fuel`. The termination
  argument does not disappear, it moves into a theorem: `goF_eq` says that fuel larger than
  `cost row below` (entries left in the current row, plus one more than the length of each
  row below) gives `some (Zipper.go …)`. Each step lowers `cost` by at least one. This is a
  single numeric measure, where `Zipper.go` needed a lexicographic pair: the fuel bound is
  allowed to be crude.
* Kernel evaluation: `goF` reduces in the kernel, so `decide` checks concrete insertions and
  whole RSK runs (examples below). `Zipper.ins` is defined by well-founded recursion, which
  does not reduce: `decide` gets stuck, and only `#guard` (compiled code) works on it.
* Proof shape: `goF_eq` is an induction on the fuel, with the same two cases as the loop.
  `goF_mono` (more fuel never changes a `some` answer) is the same induction. Neither needs
  sortedness or any other invariant of the tableau.
* Statement contortions: every theorem about `goF` carries a fuel hypothesis, and `ins`
  needs a default for the `none` branch that is never taken. Proofs about `ins` go through
  `ins_eq_zipper`, then `Zipper.ins_eq` to `Nested.ins`.
* `partial def`: Lean compiles `goP` but adds it to the environment as an `opaque`
  constant. The kernel cannot unfold it, so no equation about its values is provable: not
  `rfl`, not `decide`, not `unfold`, not `simp [goP]` (see the comment at the end). The only
  facts available are those that hold for any function of its type. `#guard` runs it.
  `implemented_by` can make it the compiled code of a total definition (`insC`), so
  programs get the fast loop while proofs see the fuel version.
* Use: fuel for computation in the kernel, equality with a proved version for theorems.
  `unrsk_rsk` below is transferred from `Nested.unrsk_rsk` in one line.

## Main results

* `goF_eq`: with fuel above `cost row below`, `goF` returns `some` of what `Zipper.go`
  returns.
* `goF_mono`: if `goF` succeeds with some fuel, it gives the same answer with more fuel.
* `insF_bound`, `ins_eq_zipper`, `ins_eq_nested`: `bound t` fuel always suffices, and then
  the result is `Zipper.ins x t = Nested.ins x t`.
* `rsk_eq`, `unrsk_rsk`: RSK built on the fuel insertion equals `Nested.rsk`, so
  `Nested.unrsk` inverts it.
-/

namespace RMT.RSK.Fuel

open RMT.RSK

/-! ## The loop with fuel -/

/-- `Zipper.go` with an explicit step counter: the same state (rows `above`, the current
row split at the cursor into `pre` and `row`, rows `below`) and the same two moves. Returns
`none` when the fuel runs out. -/
def goF (x : Nat) (above : Tab) (pre : Row) : Nat → Row → Tab → Option (Tab × Nat)
  | 0, _, _ => none
  | _ + 1, [], below => some (above.reverse ++ (pre.reverse ++ [x]) :: below, above.length)
  | n + 1, y :: ys, below =>
    if x < y then goF y ((pre.reverse ++ x :: ys) :: above) [] n (below.headD []) below.tail
    else goF x above (y :: pre) n ys below

/-- Number of boxes plus number of rows. -/
def weight : Tab → Nat
  | [] => 0
  | r :: rs => r.length + 1 + weight rs

/-- Steps the loop may still take: the entries left in the current row, plus each row
below together with the bump that enters it. -/
def cost (row : Row) (below : Tab) : Nat := row.length + weight below

/-- Fuel for inserting into `t`: number of boxes plus number of rows plus one. -/
def bound (t : Tab) : Nat := weight t + 1

/-- Insertion with explicit fuel. -/
def insF (x : Nat) (t : Tab) (fuel : Nat) : Option (Tab × Nat) :=
  goF x [] [] fuel (t.headD []) t.tail

/-- Insertion with the fuel `bound t`. The default `([], 0)` is never used (`insF_bound`). -/
def ins (x : Nat) (t : Tab) : Tab × Nat := (insF x t (bound t)).getD ([], 0)

/-! ## Enough fuel gives the answer of `Zipper.go` -/

theorem cost_bump (y : Nat) (ys : Row) (below : Tab) :
    cost (below.headD []) below.tail + 1 ≤ cost (y :: ys) below := by
  cases below <;> simp [cost, weight] <;> omega

/-- **Enough fuel suffices.** With fuel above `cost row below`, the loop finishes and agrees
with `Zipper.go`. Induction on the fuel, following the two moves of the loop. -/
theorem goF_eq (x : Nat) (n : Nat) : ∀ (above : Tab) (pre row : Row) (below : Tab),
    cost row below < n → goF x above pre n row below = some (Zipper.go x above pre row below) := by
  induction n generalizing x with
  | zero => intro _ _ _ _ h; omega
  | succ n ih =>
    intro above pre row below h
    cases row with
    | nil => unfold Zipper.go; rfl
    | cons y ys =>
      unfold goF Zipper.go
      split
      · rename_i hxy
        exact ih y _ _ _ _ (by have := cost_bump y ys below; omega)
      · exact ih x _ _ _ _ (by simp [cost] at h ⊢; omega)

/-- **Fuel monotonicity.** Once the loop succeeds, more fuel gives the same answer. -/
theorem goF_mono (x : Nat) (n : Nat) : ∀ (m : Nat) (above : Tab) (pre row : Row) (below : Tab)
    (r : Tab × Nat), n ≤ m → goF x above pre n row below = some r →
    goF x above pre m row below = some r := by
  induction n generalizing x with
  | zero => intro _ _ _ _ _ _ _ h; simp [goF] at h
  | succ n ih =>
    intro m above pre row below r hnm h
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases row with
    | nil => exact h
    | cons y ys =>
      unfold goF at h ⊢
      split
      · rename_i hxy; simp only [hxy, ↓reduceIte] at h; exact ih y m _ _ _ _ r (by omega) h
      · rename_i hxy; simp only [hxy, ↓reduceIte] at h; exact ih x m _ _ _ _ r (by omega) h

theorem cost_head (t : Tab) : cost (t.headD []) t.tail < bound t := by
  cases t <;> simp [cost, bound, weight] <;> omega

/-- `bound t` fuel always suffices, and the answer is the zipper insertion. -/
theorem insF_bound (x : Nat) (t : Tab) : insF x t (bound t) = some (Zipper.ins x t) :=
  goF_eq x _ [] [] _ _ (cost_head t)

/-- Any fuel at least `bound t` gives the zipper insertion. -/
theorem insF_ge (x : Nat) (t : Tab) (n : Nat) (h : bound t ≤ n) :
    insF x t n = some (Zipper.ins x t) :=
  goF_mono x _ n [] [] _ _ _ h (insF_bound x t)

theorem ins_eq_zipper (x : Nat) (t : Tab) : ins x t = Zipper.ins x t := by
  simp [ins, insF_bound]

theorem ins_eq_nested (x : Nat) (t : Tab) : ins x t = Nested.ins x t := by
  rw [ins_eq_zipper, Zipper.ins_eq]

/-! ## RSK on the fuel insertion, and invertibility by transfer -/

/-- RSK with the fuel insertion, right to left as in `Nested.rsk`. -/
def rsk : List Nat → Tab × List Nat
  | [] => ([], [])
  | x :: w => let p := rsk w; let q := ins x p.1; (q.1, q.2 :: p.2)

theorem rsk_eq : ∀ w, rsk w = Nested.rsk w
  | [] => rfl
  | x :: w => by simp only [rsk, Nested.rsk, rsk_eq w, ins_eq_nested]

/-- RSK on the fuel insertion is inverted by `Nested.unrsk`: a transfer, no new proof. -/
theorem unrsk_rsk (w : List Nat) : Nested.unrsk (rsk w).1 (rsk w).2 = w := by
  rw [rsk_eq]; exact Nested.unrsk_rsk w

/-! ## The kernel evaluates it -/

example : ins 2 [[1, 3], [4]] = ([[1, 2], [3], [4]], 2) := by decide
example : ins 5 [[1, 3], [4]] = ([[1, 3, 5], [4]], 0) := by decide
example : insF 2 [[1, 3], [4]] 2 = none := by decide
example : rsk [2, 4, 1, 3, 1] = ([[1, 1, 2], [3, 4]], [1, 0, 1, 0, 0]) := by decide
-- `example : Zipper.ins 2 [[1, 3], [4]] = ([[1, 2], [3], [4]], 2) := by decide` fails: the
-- well-founded recursion in `Zipper.go` does not reduce. Only compiled evaluation works:
#guard Zipper.ins 2 [[1, 3], [4]] == ([[1, 2], [3], [4]], 2)

/-! ## The same loop as a `partial def` -/

/-- The loop of `Zipper.go` with no termination argument. Lean compiles it, but the kernel
only sees an `opaque` constant of this type. -/
partial def goP (x : Nat) (above : Tab) (pre : Row) : Row → Tab → Tab × Nat
  | [], below => (above.reverse ++ (pre.reverse ++ [x]) :: below, above.length)
  | y :: ys, below =>
    if x < y then goP y ((pre.reverse ++ x :: ys) :: above) [] (below.headD []) below.tail
    else goP x above (y :: pre) ys below

/-- Insertion by the partial loop. -/
def insP (x : Nat) (t : Tab) : Tab × Nat := goP x [] [] (t.headD []) t.tail

#guard insP 2 [[1, 3], [4]] == ([[1, 2], [3], [4]], 2)
#guard insP 2 [[1, 3], [4]] == ins 2 [[1, 3], [4]]

/-
Nothing about the values of `goP` can be proved. Each of these fails, even on the base case:

example : goP 1 [] [] [] [] = ([[1]], 0) := by rfl         -- not definitionally equal
example : goP 1 [] [] [] [] = ([[1]], 0) := by decide      -- instance does not reduce
example : goP 1 [] [] [] [] = ([[1]], 0) := by unfold goP  -- failed to unfold `goP`
example : goP 1 [] [] [] [] = ([[1]], 0) := by simp [goP]  -- no progress

`#print goP` shows `opaque goP : Nat → Tab → Row → Row → Tab → Tab × Nat`. The `partial`
keyword only asks that the type be inhabited, which `Tab × Nat` is. Any function of this
type would be a consistent value for `goP`, so the only provable facts are those true of all
of them, such as the following.
-/

/-- All that is known about `goP`: it is some function of its type. -/
theorem goP_trivial : ∃ f : Nat → Tab → Row → Row → Tab → Tab × Nat, f = goP := ⟨_, rfl⟩

/-- The fuel insertion, compiled to the partial loop. The kernel and all proofs see the
body, which is `ins`; `#eval` runs `insP`. Sound in spirit because `ins = Zipper.ins`, and
`goP` runs the same code as `Zipper.go`; Lean does not check this. -/
@[implemented_by insP]
def insC (x : Nat) (t : Tab) : Tab × Nat := ins x t

theorem insC_eq (x : Nat) (t : Tab) : insC x t = Nested.ins x t := ins_eq_nested x t

example : insC 2 [[1, 3], [4]] = ([[1, 2], [3], [4]], 2) := by decide
#guard insC 2 [[1, 3], [4]] == ([[1, 2], [3], [4]], 2)

end RMT.RSK.Fuel
