import RMTlib.RSK.Basic

/-!
# Jeu de taquin slides: recursion on a sum measure

A forward slide (Schützenberger's jeu de taquin) starts with a hole at an inner corner of a
skew tableau. At each step an entry moves into the hole from the right or from below:

* if only one of the two cells is filled, its entry moves;
* if both are filled, with `a` to the right and `b` below, then `b` moves up when `b ≤ a`,
  and `a` moves left when `a < b`.

Ties go to the entry below. This is the standard rule for semistandard tableaux: moving
`a = b` left would put it directly above an equal entry, which breaks column strictness.
The slide stops when nothing is to the right or below (an outer corner); that cell then
leaves the shape. The reverse slide `rev` is the mirror image: the hole moves left or up,
the larger of the entries to the left and above moves in (on ties, the one above), and it
stops at an inner corner.

## Representation

A filling is a function `Fill := Nat → Nat → Option Nat` (row, column ↦ entry). A skew
shape has rows that start at different columns, so with `Tab = List (List Nat)` each row
would need an offset, and every step of a slide would edit two rows at once. As a function,
a step is two point updates (`move`), the hole is just a `none`, and the tableau conditions
are local statements about a cell and its right or lower neighbour (`RowOK`, `ColOK`). The
cost is that the filling has no built-in size, so the forward slide takes a bound `n` and
treats cells outside the `n × n` square as empty (`look`).

## The recursion scheme and what it costs

`fwd` recurses on `(n - i) + (n - j)` for the hole at `(i, j)`, and `rev` on `i + j`. These
are sums, not the size of any one argument, and not lexicographic pairs as in
`RMT.RSK.Zipper` or `RMT.RSK.Growth`. Concretely:

* The hole moves right or down, so neither coordinate alone decreases, but the sum does,
  by exactly one at every step. So the measure also bounds the number of steps:
  `fwdFuel_eq` shows that fuel equal to the measure is enough.
* Termination is not about any data shrinking. It needs the fact that the step stays
  inside the square: `j + 1 < n` when the cell to the right is filled. That fact comes from
  the lookup, so `fwd` matches with `hr : look … = some a` and the `decreasing_by` uses
  `lt_of_look hr`. In a hand-written proof by the same recursion these match hypotheses
  are not visible to `decreasing_by` by name, so the proof states `have := lt_of_look hr`
  before each recursive call.
* The proofs track the position of the hole, not list lengths. The invariants are 2D:
  `Ahead` says the conditions hold strictly below row `i` or strictly right of column `j`
  (the cells the slide has not touched yet); `Inv` adds four comparisons across the hole
  (left vs below, up vs right, up vs below, left vs right) and the shape.
* `fwd` is well-founded recursion, so the kernel does not unfold it and `decide` fails on
  it. `#guard` (compiled evaluation) works. The fuel version `fwdFuel` is structural, and
  `decide` evaluates it.

Each main proof is again one recursion on the slide. `rev_fwd`, `fwd_inv`, `fwd_stopped'`
and `fwdFuel_eq` use `fun_induction fwd`; `fwd_stopped` is the same theorem as
`fwd_stopped'` written by hand with `termination_by`/`decreasing_by`. `fun_induction` was
nicer: no measure to repeat, no `rw [fwd]; split`, the match hypotheses arrive as named
case arguments, and cases with the same move can share one branch. Its cost is that the
cases are only numbered (`case1` … `case5`, in the order of the match arms), so one has to
know the definition to read the proof.

The inverse theorem is a loop invariant: `rev (fwd T) = rev T` for every intermediate
state (`rev_fwd`), and `rev` stops at once at an inner corner. Each step of `rev` undoes a
step of `fwd` (`undo_right`, `undo_down`); for this only the conditions on the untouched
region are needed (`Ahead`), not the shape. Preservation (`fwd_tableau`) needs more: the
comparisons across the hole, and order-convexity of the shape in one case (moving `b` up
when nothing is to the right of the hole).

## Main results

* `rev_fwd_corner`: from the outer corner where the forward slide stopped, the reverse slide
  returns the original tableau and the original inner corner.
* `fwd_tableau`: the forward slide sends a tableau on a skew shape with a hole at an inner
  corner to a tableau on the same shape minus the cell where the hole stopped.
* `fwd_stopped`, `fwd_stopped'`: the hole stops at an outer corner, weakly south-east of its
  start (hand-written recursion, and `fun_induction`).
* `fwdFuel_eq`: a structural version with fuel equal to the measure computes `fwd`.

## Scope

Only single slides. Rectification (sliding until the shape is straight) and Schützenberger's
theorem that it gives the insertion tableau are not treated. `fwd_tableau` is stated for
fillings bounded by `n`; `rev_fwd_corner` needs no bound.
-/

namespace RMT.RSK.JeuDeTaquin

/-- A filling of the grid: `T i j` is the entry in row `i`, column `j`, or `none`. -/
abbrev Fill := Nat → Nat → Option Nat

/-- Overwrite one cell. -/
def set (T : Fill) (i j : Nat) (v : Option Nat) : Fill :=
  fun r c => if r = i ∧ c = j then v else T r c

/-- Move the entry at `(r, c)` into `(r', c')`, leaving `(r, c)` empty. -/
def move (T : Fill) (r c r' c' : Nat) : Fill := set (set T r' c' (T r c)) r c none

/-- Look up a cell, treating everything outside the `n × n` square as empty. -/
def look (n : Nat) (T : Fill) (i j : Nat) : Option Nat :=
  if i < n ∧ j < n then T i j else none

theorem lt_of_look {n : Nat} {T : Fill} {i j a : Nat} (h : look n T i j = some a) :
    i < n ∧ j < n := by
  unfold look at h; split at h <;> simp_all

/-- The forward slide with its hole at `(i, j)`. Returns the final filling and the cell
where the hole stopped (still `none`; it is the cell that leaves the shape). Ties go to the
entry below. Measure `(n - i) + (n - j)`, which drops by one at each step. -/
def fwd (n : Nat) (T : Fill) (i j : Nat) : Fill × Nat × Nat :=
  match hr : look n T i (j + 1), hb : look n T (i + 1) j with
  | none, none => (T, i, j)
  | some _, none => fwd n (move T i (j + 1) i j) i (j + 1)
  | none, some _ => fwd n (move T (i + 1) j i j) (i + 1) j
  | some a, some b =>
    if b ≤ a then fwd n (move T (i + 1) j i j) (i + 1) j
    else fwd n (move T i (j + 1) i j) i (j + 1)
termination_by (n - i) + (n - j)
decreasing_by
  all_goals first
    | (have := lt_of_look hr; omega)
    | (have := lt_of_look hb; omega)

/-- The entry left of `(i, j)`, if any. -/
def leftOf (T : Fill) (i j : Nat) : Option Nat := if j = 0 then none else T i (j - 1)
/-- The entry above `(i, j)`, if any. -/
def upOf (T : Fill) (i j : Nat) : Option Nat := if i = 0 then none else T (i - 1) j

theorem ne_of_leftOf {T : Fill} {i j a : Nat} (h : leftOf T i j = some a) : j ≠ 0 := by
  unfold leftOf at h; split at h <;> simp_all
theorem ne_of_upOf {T : Fill} {i j a : Nat} (h : upOf T i j = some a) : i ≠ 0 := by
  unfold upOf at h; split at h <;> simp_all

/-- The reverse slide with its hole at `(i, j)`: the larger of the entries to the left and
above moves in (ties go to the entry above), until nothing is left or above. Returns the
final filling and the cell where the hole stopped. Measure `i + j`. -/
def rev (T : Fill) (i j : Nat) : Fill × Nat × Nat :=
  match hl : leftOf T i j, hu : upOf T i j with
  | none, none => (T, i, j)
  | some _, none => rev (move T i (j - 1) i j) i (j - 1)
  | none, some _ => rev (move T (i - 1) j i j) (i - 1) j
  | some l, some u =>
    if l ≤ u then rev (move T (i - 1) j i j) (i - 1) j
    else rev (move T i (j - 1) i j) i (j - 1)
termination_by i + j
decreasing_by
  all_goals first
    | (have := ne_of_leftOf hl; omega)
    | (have := ne_of_upOf hu; omega)


theorem move_apply (T : Fill) (r c r' c' x y : Nat) :
    move T r c r' c' x y
      = if x = r ∧ y = c then none else if x = r' ∧ y = c' then T r c else T x y := rfl

theorem move_move {T : Fill} {r c r' c' : Nat} (h : T r' c' = none) (hne : ¬(r = r' ∧ c = c')) :
    move (move T r c r' c') r' c' r c = T := by
  funext x y
  simp only [move_apply]
  by_cases h1 : x = r ∧ y = c
  · obtain ⟨rfl, rfl⟩ := h1
    have : ¬(r' = x ∧ c' = y) := fun h' => hne ⟨h'.1.symm, h'.2.symm⟩
    simp [hne, this]
  · by_cases h2 : x = r' ∧ y = c'
    · obtain ⟨rfl, rfl⟩ := h2; simp [h]
    · simp [h1, h2]

theorem look_some {n : Nat} {T : Fill} {i j a : Nat} (h : look n T i j = some a) :
    T i j = some a := by
  unfold look at h; split at h <;> simp_all

/-- Rows weakly increase from `(r, c)` to `(r, c + 1)` (when both are filled). -/
def RowOK (T : Fill) (r c : Nat) : Prop := ∀ a b, T r c = some a → T r (c + 1) = some b → a ≤ b

/-- Columns strictly increase from `(r, c)` to `(r + 1, c)` (when both are filled). -/
def ColOK (T : Fill) (r c : Nat) : Prop := ∀ a b, T r c = some a → T (r + 1) c = some b → a < b

/-- The tableau conditions hold at every cell strictly below row `i` or strictly right of
column `j`: the part of the grid a slide with its hole at `(i, j)` has not touched. -/
def Ahead (T : Fill) (i j : Nat) : Prop := ∀ r c, (i < r ∨ j < c) → RowOK T r c ∧ ColOK T r c

theorem rev_stop {T : Fill} {i j : Nat} (hl : leftOf T i j = none) (hu : upOf T i j = none) :
    rev T i j = (T, i, j) := by
  rw [rev]; split <;> simp_all

theorem rev_left {T : Fill} {i j l : Nat} (hl : leftOf T i j = some l)
    (hu : ∀ u, upOf T i j = some u → u < l) :
    rev T i j = rev (move T i (j - 1) i j) i (j - 1) := by
  rw [rev]; split
  · simp_all
  · rfl
  · simp_all
  · next l' u hl' hu' =>
    have := hu u hu'; simp_all; omega

theorem rev_up {T : Fill} {i j u : Nat} (hu : upOf T i j = some u)
    (hl : ∀ l, leftOf T i j = some l → l ≤ u) :
    rev T i j = rev (move T (i - 1) j i j) (i - 1) j := by
  rw [rev]; split
  · simp_all
  · simp_all
  · rfl
  · next l u' hl' hu' =>
    have := hl l hl'; simp_all


/-! ## One step back undoes one step forward -/

theorem move_ne {T : Fill} {r c r' c' x y : Nat} (h : ¬(x = r ∧ y = c)) (h' : ¬(x = r' ∧ y = c')) :
    move T r c r' c' x y = T x y := by
  simp only [move_apply]; rw [if_neg h, if_neg h']

theorem moveR_far {T : Fill} {i j x y : Nat} (h : i < x ∨ j + 1 < y) :
    move T i (j + 1) i j x y = T x y := by
  simp only [move_apply]; rw [if_neg (by omega), if_neg (by omega)]

theorem moveD_far {T : Fill} {i j x y : Nat} (h : i + 1 < x ∨ j < y) :
    move T (i + 1) j i j x y = T x y := by
  simp only [move_apply]; rw [if_neg (by omega), if_neg (by omega)]

theorem Ahead.right {T : Fill} {i j : Nat} (hA : Ahead T i j) :
    Ahead (move T i (j + 1) i j) i (j + 1) := by
  intro r c h
  obtain ⟨hr, hc⟩ := hA r c (by omega)
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [moveR_far (by omega), moveR_far (by omega)]; exact hr a b
  · rw [moveR_far (by omega), moveR_far (by omega)]; exact hc a b

theorem Ahead.down {T : Fill} {i j : Nat} (hA : Ahead T i j) :
    Ahead (move T (i + 1) j i j) (i + 1) j := by
  intro r c h
  obtain ⟨hr, hc⟩ := hA r c (by omega)
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [moveD_far (by omega), moveD_far (by omega)]; exact hr a b
  · rw [moveD_far (by omega), moveD_far (by omega)]; exact hc a b

/-- Undo a step to the right: the entry `a` that moved left is the larger neighbour of the
new hole, because the entry above it (if any) is smaller by column strictness. -/
theorem undo_right {T : Fill} {i j a : Nat} (h0 : T i j = none) (ha : T i (j + 1) = some a)
    (hA : Ahead T i j) : rev (move T i (j + 1) i j) i (j + 1) = rev T i j := by
  have hl : leftOf (move T i (j + 1) i j) i (j + 1) = some a := by
    simp [leftOf, move_apply, ha]
  rw [rev_left hl]
  · simp only [Nat.add_sub_cancel]; rw [move_move h0 (by omega)]
  · intro u hu
    have hi := ne_of_upOf hu
    simp only [upOf, if_neg hi] at hu
    rw [move_ne (by omega) (by omega)] at hu
    exact (hA (i - 1) (j + 1) (by omega)).2 u a hu (by rw [Nat.sub_add_cancel (by omega)]; exact ha)

/-- Undo a step down: the entry `b` that moved up is the larger neighbour of the new hole
(ties go to it), because the entry to its left (if any) is weakly smaller. -/
theorem undo_down {T : Fill} {i j b : Nat} (h0 : T i j = none) (hb : T (i + 1) j = some b)
    (hA : Ahead T i j) : rev (move T (i + 1) j i j) (i + 1) j = rev T i j := by
  have hu : upOf (move T (i + 1) j i j) (i + 1) j = some b := by
    simp [upOf, move_apply, hb]
  rw [rev_up hu]
  · simp only [Nat.add_sub_cancel]; rw [move_move h0 (by omega)]
  · intro l hl
    have hj := ne_of_leftOf hl
    simp only [leftOf, if_neg hj] at hl
    rw [move_ne (by omega) (by omega)] at hl
    exact (hA (i + 1) (j - 1) (by omega)).1 l b hl (by rw [Nat.sub_add_cancel (by omega)]; exact hb)

/-- Run `rev` on a state given as a triple. -/
def revS (s : Fill × Nat × Nat) : Fill × Nat × Nat := rev s.1 s.2.1 s.2.2

/-- The reverse slide, run from wherever the forward slide stopped, ends where the reverse
slide from the start ends. Proved with `fun_induction`. -/
theorem rev_fwd (n : Nat) (T : Fill) (i j : Nat) (h0 : T i j = none) (hA : Ahead T i j) :
    revS (fwd n T i j) = rev T i j := by
  fun_induction fwd n T i j with
  | case1 => rfl
  | case2 T i j a hr hb ih =>
    rw [ih (by simp [move_apply]) hA.right, undo_right h0 (look_some hr) hA]
  | case3 T i j b hr hb ih =>
    rw [ih (by simp [move_apply]) hA.down, undo_down h0 (look_some hb) hA]
  | case4 T i j a b hr hb hba ih =>
    rw [ih (by simp [move_apply]) hA.down, undo_down h0 (look_some hb) hA]
  | case5 T i j a b hr hb hba ih =>
    rw [ih (by simp [move_apply]) hA.right, undo_right h0 (look_some hr) hA]


/-- Every cell satisfies the row and column conditions. -/
def Tableau (T : Fill) : Prop := ∀ r c, RowOK T r c ∧ ColOK T r c

/-- `(i, j)` is an inner corner: it is empty, and so are its left and upper neighbours. -/
def InnerCorner (T : Fill) (i j : Nat) : Prop :=
  T i j = none ∧ leftOf T i j = none ∧ upOf T i j = none

/-- **Reverse slide undoes forward slide.** From the outer corner where the forward slide
stopped, the reverse slide returns the original filling and the original inner corner. -/
theorem rev_fwd_corner (n : Nat) {T : Fill} {i j : Nat} (hT : Tableau T)
    (hc : InnerCorner T i j) : revS (fwd n T i j) = (T, i, j) := by
  rw [rev_fwd n T i j hc.1 (fun r c _ => hT r c), rev_stop hc.2.1 hc.2.2]

/-! ## Where the forward slide stops -/

/-- The forward slide from `(i, j)` stopped at state `s`: the hole moved weakly south-east,
is still empty, and has nothing to its right or below (it is an outer corner). -/
def Stopped (n : Nat) (i j : Nat) (s : Fill × Nat × Nat) : Prop :=
  i ≤ s.2.1 ∧ j ≤ s.2.2 ∧ s.1 s.2.1 s.2.2 = none ∧
    look n s.1 s.2.1 (s.2.2 + 1) = none ∧ look n s.1 (s.2.1 + 1) s.2.2 = none

theorem Stopped.mono {n i j i' j' : Nat} {s : Fill × Nat × Nat} (h : Stopped n i' j' s)
    (hi : i ≤ i') (hj : j ≤ j') : Stopped n i j s :=
  ⟨Nat.le_trans hi h.1, Nat.le_trans hj h.2.1, h.2.2⟩

/-- The forward slide stops at an outer corner, weakly south-east of where it started.
A hand-written recursion with the same measure and `decreasing_by` as `fwd`. -/
theorem fwd_stopped (n : Nat) (T : Fill) (i j : Nat) (h0 : T i j = none) :
    Stopped n i j (fwd n T i j) := by
  rw [fwd]
  split
  · next hr hb => exact ⟨Nat.le_refl _, Nat.le_refl _, h0, hr, hb⟩
  · next a hr hb =>
    have := lt_of_look hr
    exact (fwd_stopped n _ i (j + 1) (by simp [move_apply])).mono (Nat.le_refl _) (by omega)
  · next b hr hb =>
    have := lt_of_look hb
    exact (fwd_stopped n _ (i + 1) j (by simp [move_apply])).mono (by omega) (Nat.le_refl _)
  · next a b hr hb =>
    have := lt_of_look hr
    have := lt_of_look hb
    split
    · exact (fwd_stopped n _ (i + 1) j (by simp [move_apply])).mono (by omega) (Nat.le_refl _)
    · exact (fwd_stopped n _ i (j + 1) (by simp [move_apply])).mono (Nat.le_refl _) (by omega)
termination_by (n - i) + (n - j)
decreasing_by all_goals omega

/-- The same theorem by `fun_induction`. -/
theorem fwd_stopped' (n : Nat) (T : Fill) (i j : Nat) (h0 : T i j = none) :
    Stopped n i j (fwd n T i j) := by
  fun_induction fwd n T i j with
  | case1 T i j hr hb => exact ⟨Nat.le_refl _, Nat.le_refl _, h0, hr, hb⟩
  | case2 T i j a hr hb ih | case5 T i j a b hr hb _ ih =>
    exact (ih (by simp [move_apply])).mono (Nat.le_refl _) (by omega)
  | case3 T i j b hr hb ih | case4 T i j a b hr hb _ ih =>
    exact (ih (by simp [move_apply])).mono (by omega) (Nat.le_refl _)


/-! ## The forward slide preserves the tableau conditions -/

/-- Every filled cell lies in the `n × n` square. -/
def Bounded (n : Nat) (T : Fill) : Prop := ∀ i j, (n ≤ i ∨ n ≤ j) → T i j = none

theorem look_eq {n : Nat} {T : Fill} (hB : Bounded n T) (i j : Nat) : look n T i j = T i j := by
  unfold look; split
  · rfl
  · exact (hB i j (by omega)).symm

theorem Bounded.move {n : Nat} {T : Fill} (hB : Bounded n T) (r c : Nat) {r' c' : Nat}
    (hr : r' < n) (hc : c' < n) : Bounded n (move T r c r' c') := by
  intro x y h
  rw [move_apply]; split
  · rfl
  · rw [if_neg (by omega)]; exact hB x y h

/-- A set of cells is order-convex: with two cells it contains every cell between them.
Skew shapes `λ/μ` are exactly the finite order-convex sets. -/
def Convex (sh : Nat → Nat → Prop) : Prop :=
  ∀ r c r' c' r'' c'', sh r c → sh r'' c'' → r ≤ r' → r' ≤ r'' → c ≤ c' → c' ≤ c'' → sh r' c'

/-- The invariant of a forward slide with its hole at `(i, j)`, inside the shape `sh`.
Away from the hole the filling is a tableau. Across the hole, the cells left of and above
it are smaller than the cells right of and below it, with strictness where they will end
up in the same column. -/
structure Inv (sh : Nat → Nat → Prop) (T : Fill) (i j : Nat) : Prop where
  /-- The hole is empty. -/
  hole : T i j = none
  /-- The filled cells, together with the hole, are the shape. -/
  shape : ∀ r c, sh r c ↔ (T r c ≠ none ∨ (r = i ∧ c = j))
  /-- Rows are weakly increasing away from the hole. -/
  row : ∀ r c, RowOK T r c
  /-- Columns are strictly increasing away from the hole. -/
  col : ∀ r c, ColOK T r c
  /-- The cell left of the hole is at most the cell below it. -/
  lb : ∀ d b, leftOf T i j = some d → T (i + 1) j = some b → d ≤ b
  /-- The cell above the hole is smaller than the cell right of it. -/
  ur : ∀ u a, upOf T i j = some u → T i (j + 1) = some a → u < a
  /-- The cell above the hole is smaller than the cell below it. -/
  ub : ∀ u b, upOf T i j = some u → T (i + 1) j = some b → u < b
  /-- The cell left of the hole is at most the cell right of it. -/
  lr : ∀ d a, leftOf T i j = some d → T i (j + 1) = some a → d ≤ a

theorem leftOf_eq {T : Fill} {i j d : Nat} (h : leftOf T i j = some d) :
    j ≠ 0 ∧ T i (j - 1) = some d := by
  unfold leftOf at h; split at h
  · cases h
  · exact ⟨by assumption, h⟩

theorem upOf_eq {T : Fill} {i j u : Nat} (h : upOf T i j = some u) :
    i ≠ 0 ∧ T (i - 1) j = some u := by
  unfold upOf at h; split at h
  · cases h
  · exact ⟨by assumption, h⟩

/-- A step down keeps the invariant. This is the one place where the shape is used: if
nothing is right of the hole, nothing is diagonally below-right of it either. -/
theorem Inv.down {sh : Nat → Nat → Prop} {T : Fill} {i j b : Nat} (hC : Convex sh)
    (I : Inv sh T i j) (hb : T (i + 1) j = some b) (hle : ∀ a, T i (j + 1) = some a → b ≤ a) :
    Inv sh (move T (i + 1) j i j) (i + 1) j where
  hole := by simp [move_apply]
  shape r c := by
    rw [I.shape r c, move_apply]
    by_cases h1 : r = i + 1 ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h1; simp [hb]
    · by_cases h2 : r = i ∧ c = j
      · obtain ⟨rfl, rfl⟩ := h2; simp [hb]
      · rw [if_neg h1, if_neg h2]; simp only [h1, h2, or_false]
  row r c x y hx hy := by
    by_cases h1 : r = i + 1 ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h1; simp [move_apply] at hx
    by_cases h2 : r = i + 1 ∧ c + 1 = j
    · obtain ⟨rfl, rfl⟩ := h2; simp [move_apply] at hy
    by_cases h3 : r = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h3
      simp [move_apply, hb] at hx; subst hx
      rw [move_ne (by omega) (by omega)] at hy; exact hle y hy
    by_cases h4 : r = i ∧ c + 1 = j
    · obtain ⟨rfl, rfl⟩ := h4
      rw [move_ne (by omega) (by omega)] at hx
      simp [move_apply, hb] at hy; subst hy
      exact I.lb x _ (by simpa [leftOf] using hx) hb
    rw [move_ne (by omega) (by omega)] at hx hy; exact I.row r c x y hx hy
  col r c x y hx hy := by
    by_cases h1 : r = i + 1 ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h1; simp [move_apply] at hx
    by_cases h2 : r = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h2; simp [move_apply] at hy
    by_cases h3 : r + 1 = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h3
      rw [move_ne (by omega) (by omega)] at hx
      simp [move_apply, hb] at hy; subst hy
      exact I.ub x _ (by simpa [upOf] using hx) hb
    rw [move_ne (by omega) (by omega)] at hx hy; exact I.col r c x y hx hy
  lb d e hd he := by
    obtain ⟨hj, hd⟩ := leftOf_eq hd
    rw [move_ne (by omega) (by omega)] at hd he
    have := I.row (i + 1) (j - 1) d b hd (by rw [Nat.sub_add_cancel (by omega)]; exact hb)
    have := I.col (i + 1) j b e hb he
    omega
  ur u f hu hf := by
    obtain ⟨-, hu⟩ := upOf_eq hu
    simp [move_apply, hb] at hu; subst hu
    rw [move_ne (by omega) (by omega)] at hf
    cases ha : T i (j + 1) with
    | some a => have := hle a ha; have := I.col i (j + 1) a f ha hf; omega
    | none =>
      have h1 : sh i j := (I.shape i j).2 (Or.inr ⟨rfl, rfl⟩)
      have h2 : sh (i + 1) (j + 1) := (I.shape _ _).2 (Or.inl (by simp [hf]))
      have h3 := (I.shape i (j + 1)).1 (hC _ _ _ _ _ _ h1 h2 (by omega) (by omega) (by omega)
        (by omega))
      simp [ha] at h3
  ub u e hu he := by
    obtain ⟨-, hu⟩ := upOf_eq hu
    simp [move_apply, hb] at hu; subst hu
    rw [move_ne (by omega) (by omega)] at he
    exact I.col (i + 1) j _ e hb he
  lr d f hd hf := by
    obtain ⟨hj, hd⟩ := leftOf_eq hd
    rw [move_ne (by omega) (by omega)] at hd hf
    have := I.row (i + 1) (j - 1) d b hd (by rw [Nat.sub_add_cancel (by omega)]; exact hb)
    have := I.row (i + 1) j b f hb hf
    omega

/-- A step to the right keeps the invariant. -/
theorem Inv.right {sh : Nat → Nat → Prop} {T : Fill} {i j a : Nat}
    (I : Inv sh T i j) (ha : T i (j + 1) = some a) (hlt : ∀ b, T (i + 1) j = some b → a < b) :
    Inv sh (move T i (j + 1) i j) i (j + 1) where
  hole := by simp [move_apply]
  shape r c := by
    rw [I.shape r c, move_apply]
    by_cases h1 : r = i ∧ c = j + 1
    · obtain ⟨rfl, rfl⟩ := h1; simp [ha]
    · by_cases h2 : r = i ∧ c = j
      · obtain ⟨rfl, rfl⟩ := h2; simp [ha]
      · rw [if_neg h1, if_neg h2]; simp only [h1, h2, or_false]
  row r c x y hx hy := by
    by_cases h1 : r = i ∧ c = j + 1
    · obtain ⟨rfl, rfl⟩ := h1; simp [move_apply] at hx
    by_cases h2 : r = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h2; simp [move_apply] at hy
    by_cases h3 : r = i ∧ c + 1 = j
    · obtain ⟨rfl, rfl⟩ := h3
      rw [move_ne (by omega) (by omega)] at hx
      simp [move_apply, ha] at hy; subst hy
      exact I.lr x _ (by simpa [leftOf] using hx) ha
    rw [move_ne (by omega) (by omega)] at hx hy; exact I.row r c x y hx hy
  col r c x y hx hy := by
    by_cases h1 : r = i ∧ c = j + 1
    · obtain ⟨rfl, rfl⟩ := h1; simp [move_apply] at hx
    by_cases h2 : r + 1 = i ∧ c = j + 1
    · obtain ⟨rfl, rfl⟩ := h2; simp [move_apply] at hy
    by_cases h3 : r = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h3
      simp [move_apply, ha] at hx; subst hx
      rw [move_ne (by omega) (by omega)] at hy; exact hlt y hy
    by_cases h4 : r + 1 = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h4
      rw [move_ne (by omega) (by omega)] at hx
      simp [move_apply, ha] at hy; subst hy
      exact I.ur x _ (by simpa [upOf] using hx) ha
    rw [move_ne (by omega) (by omega)] at hx hy; exact I.col r c x y hx hy
  lb d f hd hf := by
    obtain ⟨-, hd⟩ := leftOf_eq hd
    simp [move_apply, ha] at hd; subst hd
    rw [move_ne (by omega) (by omega)] at hf
    exact Nat.le_of_lt (I.col i (j + 1) _ f ha hf)
  ur g h hg hh := by
    obtain ⟨hi, hg⟩ := upOf_eq hg
    rw [move_ne (by omega) (by omega)] at hg hh
    have := I.col (i - 1) (j + 1) g a hg (by rw [Nat.sub_add_cancel (by omega)]; exact ha)
    have := I.row i (j + 1) a h ha hh
    omega
  ub g f hg hf := by
    obtain ⟨hi, hg⟩ := upOf_eq hg
    rw [move_ne (by omega) (by omega)] at hg hf
    have := I.col (i - 1) (j + 1) g a hg (by rw [Nat.sub_add_cancel (by omega)]; exact ha)
    have := I.col i (j + 1) a f ha hf
    omega
  lr d h hd hh := by
    obtain ⟨-, hd⟩ := leftOf_eq hd
    simp [move_apply, ha] at hd; subst hd
    rw [move_ne (by omega) (by omega)] at hh
    exact I.row i (j + 1) _ h ha hh


/-- The whole forward slide keeps the invariant (and boundedness). By `fun_induction`. -/
theorem fwd_inv {sh : Nat → Nat → Prop} (hC : Convex sh) (n : Nat) (T : Fill) (i j : Nat)
    (hB : Bounded n T) (I : Inv sh T i j) :
    Bounded n (fwd n T i j).1 ∧ Inv sh (fwd n T i j).1 (fwd n T i j).2.1 (fwd n T i j).2.2 := by
  fun_induction fwd n T i j with
  | case1 => exact ⟨hB, I⟩
  | case2 T i j a hr hb ih =>
    have := lt_of_look hr
    rw [look_eq hB] at hr hb
    exact ih (hB.move _ _ (by omega) (by omega)) (I.right hr (by simp [hb]))
  | case3 T i j b hr hb ih =>
    have := lt_of_look hb
    rw [look_eq hB] at hr hb
    exact ih (hB.move _ _ (by omega) (by omega)) (I.down hC hb (by simp [hr]))
  | case4 T i j a b hr hb hba ih =>
    have := lt_of_look hb
    rw [look_eq hB] at hr hb
    exact ih (hB.move _ _ (by omega) (by omega)) (I.down hC hb (by simp_all))
  | case5 T i j a b hr hb hba ih =>
    have := lt_of_look hr
    rw [look_eq hB] at hr hb
    exact ih (hB.move _ _ (by omega) (by omega)) (I.right hr (by simp_all))

/-- **The forward slide preserves the tableau conditions.** Start from a tableau filling a
skew shape `sh` (order-convex, inside the `n × n` square) with a hole at the inner corner
`(i, j)`. After the slide, the filling is again a tableau, and it fills exactly `sh` minus
the cell where the hole stopped. -/
theorem fwd_tableau {sh : Nat → Nat → Prop} (hC : Convex sh) {n : Nat} {T : Fill} {i j : Nat}
    (hT : Tableau T) (hB : Bounded n T) (hc : InnerCorner T i j)
    (hsh : ∀ r c, sh r c ↔ (T r c ≠ none ∨ (r = i ∧ c = j))) :
    Tableau (fwd n T i j).1 ∧
      ∀ r c, sh r c ↔ ((fwd n T i j).1 r c ≠ none ∨
        (r = (fwd n T i j).2.1 ∧ c = (fwd n T i j).2.2)) := by
  have I : Inv sh T i j :=
    { hole := hc.1, shape := hsh, row := fun r c => (hT r c).1, col := fun r c => (hT r c).2
      lb := by simp [hc.2.1], ur := by simp [hc.2.2], ub := by simp [hc.2.2]
      lr := by simp [hc.2.1] }
  have I' := (fwd_inv hC n T i j hB I).2
  exact ⟨fun r c => ⟨I'.row r c, I'.col r c⟩, I'.shape⟩


/-! ## Examples, and a fuel version for `decide` -/

/-- A filling from its rows (`none` for an empty cell). -/
def ofRows (rows : List (List (Option Nat))) : Fill :=
  fun i j => match rows[i]? with
    | some r => r[j]?.getD none
    | none => none

/-- The `n × n` square of a filling, as rows. -/
def render (n : Nat) (T : Fill) : List (List (Option Nat)) :=
  (List.range n).map fun i => (List.range n).map fun j => T i j

/-- The forward slide, by structural recursion on a fuel argument. -/
def fwdFuel : Nat → Nat → Fill → Nat → Nat → Fill × Nat × Nat
  | 0, _, T, i, j => (T, i, j)
  | k + 1, n, T, i, j =>
    match look n T i (j + 1), look n T (i + 1) j with
    | none, none => (T, i, j)
    | some _, none => fwdFuel k n (move T i (j + 1) i j) i (j + 1)
    | none, some _ => fwdFuel k n (move T (i + 1) j i j) (i + 1) j
    | some a, some b =>
      if b ≤ a then fwdFuel k n (move T (i + 1) j i j) (i + 1) j
      else fwdFuel k n (move T i (j + 1) i j) i (j + 1)

/-- Fuel equal to the measure is enough: each step uses one unit of fuel and lowers the
measure by exactly one. By `fun_induction` on `fwd`, generalising the fuel. -/
theorem fwdFuel_eq (n : Nat) (T : Fill) (i j : Nat) :
    ∀ k, (n - i) + (n - j) ≤ k → fwdFuel k n T i j = fwd n T i j := by
  fun_induction fwd n T i j with
  | case1 T i j hr hb => intro k _; cases k <;> simp [fwdFuel, hr, hb]
  | case2 T i j a hr hb ih =>
    intro k hk; have := lt_of_look hr
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [fwdFuel, hr, hb]; exact ih k (by omega)
  | case3 T i j b hr hb ih =>
    intro k hk; have := lt_of_look hb
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [fwdFuel, hr, hb]; exact ih k (by omega)
  | case4 T i j a b hr hb hba ih =>
    intro k hk; have := lt_of_look hb
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [fwdFuel, hr, hb, if_pos hba]; exact ih k (by omega)
  | case5 T i j a b hr hb hba ih =>
    intro k hk; have := lt_of_look hr
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [fwdFuel, hr, hb, if_neg hba]; exact ih k (by omega)

/-- The skew tableau `[[·, 1, 3], [2, 4]]` of shape `(3, 2)/(1)`. -/
def ex₁ : Fill := ofRows [[none, some 1, some 3], [some 2, some 4]]

-- Hole at `(0, 0)`: `1 < 2` moves left, then `3 < 4` moves left; the hole ends at `(0, 2)`.
#guard render 3 (fwd 3 ex₁ 0 0).1
  = [[some 1, some 3, none], [some 2, some 4, none], [none, none, none]]
#guard (fwd 3 ex₁ 0 0).2 = (0, 2)
#guard render 3 (revS (fwd 3 ex₁ 0 0)).1 = render 3 ex₁
#guard (revS (fwd 3 ex₁ 0 0)).2 = (0, 0)

/-- A tie: `[[·, 2], [2, 3]]`. The `2` below moves up, not the `2` to the right. -/
def ex₂ : Fill := ofRows [[none, some 2], [some 2, some 3]]

#guard render 2 (fwd 2 ex₂ 0 0).1 = [[some 2, some 2], [some 3, none]]
#guard (fwd 2 ex₂ 0 0).2 = (1, 1)
#guard render 2 (revS (fwd 2 ex₂ 0 0)).1 = render 2 ex₂
#guard (revS (fwd 2 ex₂ 0 0)).2 = (0, 0)

-- `decide` cannot unfold `fwd`: well-founded recursion is irreducible for the kernel.
-- It does evaluate the fuel version, with the measure `(3 - 0) + (3 - 0)` as fuel.
example : render 3 (fwdFuel 6 3 ex₁ 0 0).1
    = [[some 1, some 3, none], [some 2, some 4, none], [none, none, none]] := by decide
example : (fwdFuel 6 3 ex₁ 0 0).2 = (0, 2) := by decide

end RMT.RSK.JeuDeTaquin
