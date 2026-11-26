import RMTlib.RSK.Semistandard

/-!
# RSK insertion as two mutually recursive functions

Row bumping is a machine with two states:

* `scan x pre row below`: walking along the current row with `x` in hand. `pre` holds the
  entries already passed (nearest first), `row` the entries still ahead, `below` the rows
  underneath.
* `descend y t`: `y` has just been bumped out of a row, and must be inserted into the rows
  `t` underneath.

`scan` either moves one step right (calls itself), appends `x` at the end of the row (stops),
or bumps an entry `y` and hands it to `descend`. `descend` starts a new row or starts a `scan`
of the next row. Uninsertion is not naturally mutual: its row step returns to the row above
rather than moving on, so it is the nested `Nested.unins`, and the proofs here use it.

## The recursion scheme and what it costs

What mutual recursion buys: the two levels of `Nested.ins` (along a row, down the rows)
become two named states, each with its own transitions. This is the zipper's machine
(`Zipper.go`) without the rows above, since the bumped row is put back on the way out
of the recursion.

It is not structural. Lean's mutual structural recursion needs one argument of each function,
of compatible types, that shrinks on every call. `scan` passes `below` unchanged both when it
moves right and when it calls `descend`, so `below` does not work. Its `row` argument has type
`List Nat`, while `descend` only has a `List (List Nat)` to recurse on, so Lean rejects that
pair as incompatible (`termination_by structural` fails with "descend has no compatible
argument"). The fix would be to change the data types, so we use well-founded recursion on a
single natural number (`scanWeight`, `tabWeight`): moving right drops one box from the part
of the row still ahead, and each change of state lowers the weight by at least one.

The measure is a single `Nat` on purpose. With the lexicographic measure
`(below.length, row.length)` of `Zipper.go`, the kernel does not evaluate `ins`, even with
`decide +kernel`. With a `Nat` measure, `decide +kernel` works, and after `unseal` plain
`decide` works too (see the examples at the end).

The cost in proofs: statements about `scan` and `descend` must be made together, as a
`mutual` block of theorems with the same measures, or as the two motives of the generated
principle `scan.mutual_induct`. The `scan` statement is a loop invariant. It is stated for
every prefix `pre` already passed (all entries `≤ x`), as in the zipper proofs. The
`descend` statement is the plain one. Both are shown here: `scan_eq`/`descend_eq` as a mutual
theorem block, `unins_scan`/`unins_descend` with `scan.mutual_induct`.

## Main results

* `scan_eq`, `descend_eq`, `ins_eq`: equal to `Nested.ins`, by mutual induction.
* `unins_scan`, `unins_descend`, `unins_ins`: `Nested.unins` undoes `ins`, proved directly by
  mutual induction. It uses only the row-level lemma `Nested.rowUnins_rowIns`, not the
  tableau-level `Nested.unins_ins`.
* `unrsk_rsk`: `Nested.unrsk` inverts `rsk`. That the tableaux stay `Good` is transferred
  from `Nested.ins_good` through `ins_eq`.
-/

namespace RMT.RSK.Mutual

open RMT.RSK

/-- The measure for `descend`: twice the number of rows plus twice the number of boxes. -/
def tabWeight (t : Tab) : Nat := 2 * t.length + 2 * (t.map List.length).sum

/-- The measure for `scan`: the weight of the rows below, plus one, plus the boxes still
ahead in the current row. -/
def scanWeight (row : Row) (below : Tab) : Nat := tabWeight below + 1 + row.length

mutual

/-- State 1: walk along the current row, with `x` in hand. The row is `pre.reverse ++ row`,
the cursor sits before `row`, and `below` is the rest of the tableau. Returns the new rows
from here down and the index, counted from this row, of the row that gains a box. -/
def scan (x : Nat) (pre : Row) : Row → Tab → Tab × Nat
  | [], below => ((pre.reverse ++ [x]) :: below, 0)
  | y :: ys, below =>
    if x < y then
      let p := descend y below
      ((pre.reverse ++ x :: ys) :: p.1, p.2 + 1)
    else scan x (y :: pre) ys below
termination_by row below => scanWeight row below
decreasing_by all_goals (simp only [scanWeight, tabWeight, List.length_cons]; omega)

/-- State 2: `y` was bumped and goes into the rows `t` below. Returns the new rows and the
index, counted from the first row of `t`, of the row that gains a box. -/
def descend (y : Nat) : Tab → Tab × Nat
  | [] => ([[y]], 0)
  | r :: rs => scan y [] r rs
termination_by t => tabWeight t
decreasing_by
  simp only [scanWeight, tabWeight, List.length_cons, List.map_cons, List.sum_cons]; omega

end

/-- Insert `x` into a tableau: `x` arrives at the top row as if bumped from above. -/
def ins (x : Nat) (t : Tab) : Tab × Nat := descend x t

/-- RSK on a word, inserting the letters from right to left, as in `Nested.rsk`. -/
def rsk : List Nat → Tab × List Nat
  | [] => ([], [])
  | x :: w => let p := rsk w; let q := ins x p.1; (q.1, q.2 :: p.2)

/-! ## Equality with the nested version, by a mutual theorem block -/

mutual

/-- From any state of `scan` (the entries passed are `≤ x`), the machine finishes as nested
insertion into the whole current row. -/
theorem scan_eq (x : Nat) (pre : Row) (row : Row) (below : Tab) (hpre : ∀ p ∈ pre, p ≤ x) :
    scan x pre row below = Nested.ins x ((pre.reverse ++ row) :: below) := by
  have hrev : ∀ p ∈ pre.reverse, p ≤ x := fun p hp => hpre p (List.mem_reverse.mp hp)
  match row with
  | [] =>
    rw [scan]
    simp [Nested.ins, Nested.rowIns_append x pre.reverse hrev]
  | y :: ys =>
    rw [scan]
    split
    · rename_i hxy
      have hrow : Nested.rowIns x (y :: ys) = (x :: ys, some y) := by simp [Nested.rowIns, hxy]
      simp only [Nested.ins, Zipper.rowIns_prefix x _ _ hrev, hrow]
      rw [descend_eq y below]
    · rename_i hxy
      rw [scan_eq x (y :: pre) ys below (fun p hp => by
        simp at hp; rcases hp with rfl | hp
        · omega
        · exact hpre p hp)]
      simp
termination_by scanWeight row below
decreasing_by all_goals (simp only [scanWeight, tabWeight, List.length_cons]; omega)

/-- `descend` is nested insertion. -/
theorem descend_eq (y : Nat) (t : Tab) : descend y t = Nested.ins y t := by
  match t with
  | [] => rw [descend]; rfl
  | r :: rs => rw [descend, scan_eq y [] r rs (by simp)]; simp
termination_by tabWeight t
decreasing_by
  simp only [scanWeight, tabWeight, List.length_cons, List.map_cons, List.sum_cons]; omega

end

/-- **The mutual insertion is the nested one.** -/
theorem ins_eq (x : Nat) (t : Tab) : ins x t = Nested.ins x t := descend_eq x t

/-! ## Uninsertion undoes insertion, directly by mutual induction -/

/-- Undoing a bump in a row whose prefix `pre` (all entries `≤ x`) was passed: a row-level
fact, from `Nested.rowUnins_rowIns`. -/
theorem rowUnins_prefix (x y : Nat) (pre ys : Row) (hpre : ∀ p ∈ pre, p ≤ x) (hxy : x < y)
    (hs : Sorted (pre.reverse ++ y :: ys)) :
    Nested.rowUnins y (pre.reverse ++ x :: ys) = (pre.reverse ++ y :: ys, x) := by
  have hrev : ∀ p ∈ pre.reverse, p ≤ x := fun p hp => hpre p (List.mem_reverse.mp hp)
  have hrow : Nested.rowIns x (pre.reverse ++ y :: ys) = (pre.reverse ++ x :: ys, some y) := by
    rw [Zipper.rowIns_prefix x _ _ hrev]; simp [Nested.rowIns, hxy]
  exact Nested.rowUnins_rowIns x y _ _ hs hrow

/-- The two invariants, as one conjunction from `scan.mutual_induct`. For `scan`: from a
state with sorted nonempty current row, `Good` rows below and passed entries `≤ x`,
uninsertion recovers that state. For `descend`: uninsertion recovers `t` and `y`. -/
theorem unins_scan_descend :
    (∀ x pre row below, Sorted (pre.reverse ++ row) → pre.reverse ++ row ≠ [] →
      (∀ p ∈ pre, p ≤ x) → Good below →
      Nested.unins (scan x pre row below).2 (scan x pre row below).1
        = ((pre.reverse ++ row) :: below, x)) ∧
    (∀ y t, Good t → Nested.unins (descend y t).2 (descend y t).1 = (t, y)) := by
  refine scan.mutual_induct
    (fun x pre row below => Sorted (pre.reverse ++ row) → pre.reverse ++ row ≠ [] →
      (∀ p ∈ pre, p ≤ x) → Good below →
      Nested.unins (scan x pre row below).2 (scan x pre row below).1
        = ((pre.reverse ++ row) :: below, x))
    (fun y t => Good t → Nested.unins (descend y t).2 (descend y t).1 = (t, y))
    ?_ ?_ ?_ ?_ ?_
  · -- end of the row: `x` was appended, and `unins 0` removes it
    intro x pre below _ hne _ _
    simp only [List.append_nil] at hne
    simp [scan, Nested.unins, hne]
  · -- bump: the rows below are restored by the `descend` invariant, then the row
    intro x pre y ys below hxy ih hs _ hpre hg
    rw [scan, ite_eq_left hxy]
    simp only [Nested.unins]
    rw [ih hg, rowUnins_prefix x y pre ys hpre hxy hs]
  · -- move right: the `scan` invariant at the next state
    intro x pre y ys below hxy ih hs _ hpre hg
    rw [scan, ite_eq_right hxy]
    have e : (y :: pre).reverse ++ ys = pre.reverse ++ y :: ys := by simp
    rw [← e]
    exact ih (by rw [e]; exact hs) (by simp) (fun p hp => by
      simp at hp; rcases hp with rfl | hp
      · omega
      · exact hpre p hp) hg
  · -- a new row `[y]`
    intro y _
    simp [descend, Nested.unins]
  · -- start scanning the next row
    intro y r rs ih hg
    rw [descend]
    have h := ih (by simpa using (hg r (by simp)).1) (by simpa using (hg r (by simp)).2)
      (by simp) hg.tail
    simpa using h

/-- Uninsertion recovers any state of `scan`. -/
theorem unins_scan (x : Nat) (pre row : Row) (below : Tab) (hs : Sorted (pre.reverse ++ row))
    (hne : pre.reverse ++ row ≠ []) (hpre : ∀ p ∈ pre, p ≤ x) (hg : Good below) :
    Nested.unins (scan x pre row below).2 (scan x pre row below).1
      = ((pre.reverse ++ row) :: below, x) :=
  unins_scan_descend.1 x pre row below hs hne hpre hg

/-- Uninsertion undoes `descend`. -/
theorem unins_descend (y : Nat) (t : Tab) (hg : Good t) :
    Nested.unins (descend y t).2 (descend y t).1 = (t, y) :=
  unins_scan_descend.2 y t hg

/-- **Uninsertion undoes insertion.** -/
theorem unins_ins (x : Nat) (t : Tab) (hg : Good t) :
    Nested.unins (ins x t).2 (ins x t).1 = (t, x) :=
  unins_descend x t hg

/-- `rsk` produces `Good` tableaux, transferred from `Nested.ins_good`. -/
theorem rsk_good : ∀ w, Good (rsk w).1
  | [] => by intro r hr; simp [rsk] at hr
  | x :: w => by
    simp only [rsk, ins_eq]; exact Nested.ins_good x _ (rsk_good w)

/-- **RSK is injective**: `Nested.unrsk` recovers the word. -/
theorem unrsk_rsk : ∀ w, Nested.unrsk (rsk w).1 (rsk w).2 = w
  | [] => by simp [rsk, Nested.unrsk]
  | x :: w => by
    simp only [rsk, Nested.unrsk]
    rw [unins_ins x _ (rsk_good w)]
    simp [unrsk_rsk w]

/-! ## Kernel evaluation

`scan` and `descend` are well-founded definitions, so they are irreducible for the
elaborator. The kernel still evaluates them, because the measure is a natural number. -/

example : ins 2 [[1, 3], [4]] = ([[1, 2], [3], [4]], 2) := by decide +kernel

unseal scan descend in
example : ins 2 [[1, 3], [4]] = ([[1, 2], [3], [4]], 2) := by decide

example : rsk [2, 1, 3] = ([[1, 2], [3]], [0, 1, 0]) := by decide +kernel

end RMT.RSK.Mutual
