import RMTlib.RSK.Semistandard
import RMTlib.RSK.GrowthGeneric

/-!
# The same theorems by functional induction

`RMT.RSK.Zipper`, `RMT.RSK.Growth` and `RMT.RSK.GrowthGeneric` define their loops by
well-founded recursion, and prove every loop theorem by a second, hand-written well-founded
recursion with its own `termination_by` (and often `decreasing_by`). This file changes the
proof technique and nothing else. The functions are the same. Each theorem below is proved
with the `fun_induction` tactic, which applies the induction principle Lean generates for the
function (`Zipper.go.induct`, …). No proof here has a `termination_by` or a `decreasing_by`.
Each theorem has a primed name and the exact statement of the original, checked by an
`example` right after it.

## The generated principles

Lean 4.33 generates `f.induct` for every recursive `f`, and `fun_induction f a b c` applies
it to the call `f a b c` in the goal. It uses the `f.induct_unfolding` variant, so in each
case the call is already replaced by the right-hand side of that branch.

* `Zipper.go.induct`: the motive is `Nat → Tab → Row → Row → Tab → Prop`, over ALL five
  arguments `x above pre row below`. Nothing is fixed, so the accumulators `above` and `pre`
  vary in the induction hypothesis for free. Three cases: `row = []`; `row = y :: ys` with
  `x < y` (bump, IH at `y`, a new row above, `pre = []`, `below.headD []`, `below.tail`);
  `row = y :: ys` with `¬ x < y` (skip, IH at `y :: pre`, `ys`).
* `Zipper.up.induct`: motive over all five arguments `y above rev done below`. Four cases,
  because the `match above` inside the `if` is split as well: `rev = []`; swap at the top
  row (`above = []`, no IH); swap below it (`above = a :: as`, IH); skip (IH).
* `Growth.grow.induct`: motive `Nat → Nat → Prop` over `i j`; `σ` and `N` are dropped since
  no case needs them. Three cases: `i = 0`; `j = 0` with `i ≠ 0`; `(i+1, j+1)` with three
  IHs at `(i, j)`, `(i+1, j)`, `(i, j+1)`.
* `Growth.back.induct`: `n` is a fixed parameter, the motive is over `i j`, and `top`,
  `right` do not appear. Three cases, one per `if` branch, each carrying the branch
  conditions (`n ≤ i`; `¬ n ≤ i`, `n ≤ j`; both negated, with three IHs).
  `GrowthGeneric.back.induct` is the same with two fixed parameters `n m`.
* `Nested.ins.induct`: motive over `x t`. Three cases, by the `match` on `rowIns x r`, each
  with the equation `rowIns x r = (r', _)` as a hypothesis.

## The recursion scheme and what it costs

What it buys:

* No measure and no `decreasing_by`. The original `ins_up` needs
  `decreasing_by all_goals (simp_wf; subst_vars; simp [Prod.lex_def]; try omega)`.
* The cases come pre-split, with the `if` conditions and `match` equations as named
  hypotheses. The originals open every case with `unfold go; split; rename_i hxy`, and
  `ins_up` restates each step of `up` as an equation proved by `rw [up.eq_def]; simp [hzy]`
  (three of them). Here the goal already shows the unfolded branch.
* Hypotheses in the context are generalised automatically. Each proof starts with
  `intro`, then `fun_induction`, and the IH takes the hypotheses at the new arguments.

What it costs:

* The generated principles state the bump/swap IH with `(List.attach pre).reverse.unattach`
  where the goal has `pre.reverse` (an artefact of how the well-founded definition is
  compiled). Every case that uses such an IH needs
  `simp only [List.unattach_reverse, List.unattach_attach] at ih` first.
* Case names are `case1`, `case2`, … and the variables are named by the user. One has to
  `#check` the principle to know the order and the count (`Nested.ins.induct` binds the
  `let p := ins y rs` as a case variable before the IH).
* Helpers that the original proves once inside the case must be stated before the
  induction, generalised over the case variables (`fwd` in `ins_up'`), or proved twice.
* A theorem about two calls is split along one of them only. In `back_congr'` the second
  call `back B top' right' …` is unfolded by hand in each case.

Accumulators are NOT a cost here: the motive of `go.induct` and `up.induct` ranges over
every argument, including `above` and `pre`. The original proofs had to generalise them by
stating the theorem `∀ row below, …` after fixing `x above pre` and then calling themselves
at other values of `x above pre`; `fun_induction` does the same with no extra work.

Theorems relating two different recursions also go through, as long as the conclusion is
driven by ONE call. `unins_go` goes down `go` and its conclusion is about `up` (through
`unins` and `climb`); the induction follows `go`, and the facts about `up` come from the
structural lemma `up_scan`, as in the original. The same holds for `ins_up` (follows `up`,
conclusion about `go`, via `go_scan`).

What does not fit: `Growth.square_ok`. Its recursion calls itself at `(i, j')` for every
`j' < j` and at `(i', j)` for every `i' < i` (to feed `row_flat` and `col_flat`). That is
strong induction on the lexicographic order, not the three-neighbour shape of `grow.induct`,
so no generated principle matches it. It is left as it is.

| theorem | hand-written | `fun_induction` | note |
|---|---|---|---|
| `Zipper.unins_go` | 40 | 30 | no `unfold go; split`; `unattach` cleanup in the bump case |
| `Zipper.go_good` | 41 | 37 | same steps, minus the unfolding and the measure |
| `Zipper.ins_up` | 43 | 34 | 4 cases instead of `by_cases` + `cases above`; no `up.eq_def` steps; `fwd` stated more generally |
| `Zipper.go_eq` (Semistandard) | 32 | 26 | |
| `Growth.back_grow` | 15 | 14 | `if` branches come with their conditions |
| `GrowthGeneric.back_grow` | 13 | 12 | |
| `GrowthGeneric.back_congr` | 13 | 12 | second `back` call unfolded by hand |
| `Nested.unins_ins` (structural) | 19 | 15 | no `cases hrow : rowIns x r` |

Counts are non-blank lines from `theorem` to the last line of the proof: the statement, the
proof, and in the originals `termination_by`/`decreasing_by`. The originals carry a few more
comment lines (4 in `unins_go`, 3 in `ins_up`, against 0 and 1 here). The gain is 10–25% of
the lines. The real gain is that the proofs no longer state or check termination.

## Main results

* `unins_go'`, `go_good'`, `ins_up'`, `go_eq'`: the `Zipper` loop theorems.
* `Growth.back_grow'`, `GrowthGeneric.back_grow'`, `GrowthGeneric.back_congr'`: the grid
  theorems.
* `Nested.unins_ins'`: the structural case, for comparison.
-/

namespace RMT.RSK.FunInd

open RMT.RSK

section Zipper

open RMT.RSK.Zipper

/-! ## `Zipper`: induction along `go` -/

/-- `Zipper.unins_go` by `fun_induction` along `go`. -/
theorem unins_go' (x : Nat) (above : Tab) (pre : Row) : ∀ (row : Row) (below : Tab),
    Sorted row → (∀ p ∈ pre, p ≤ x) → Good below →
    unins (go x above pre row below).2 (go x above pre row below).1
      = climb x above (mk (pre.reverse ++ row) below) := by
  intro row below hs hpre hb
  fun_induction go x above pre row below with
  | case1 x above pre below =>
    have hd : (above.reverse ++ (pre.reverse ++ [x]) :: below).drop (above.length + 1) = below := by
      simpa using drop_mid above.reverse (pre.reverse ++ [x]) below
    simp [unins, hd, List.take_left', List.getD_eq_getElem?_getD]
  | case2 x above pre y ys below hxy ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    have hy : ∀ b ∈ ys, y ≤ b := (List.pairwise_cons.mp hs).1
    have hhead : Sorted (below.headD []) := by
      cases below with
      | nil => simp [Sorted]
      | cons r rs => exact (hb r (by simp)).1
    have hmk : mk (below.headD []) below.tail = below := by
      cases below with
      | nil => simp [mk]
      | cons r rs => simp [mk, (hb r (by simp)).2]
    rw [ih hhead (by simp) (fun r h => hb r (List.mem_of_mem_tail h))]
    simp only [List.reverse_nil, List.nil_append, hmk, climb]
    have := up_scan x y above pre below hxy ys.reverse [] (by simpa using hy)
    simp only [List.reverse_append, List.reverse_cons, List.reverse_reverse,
      List.append_assoc, List.singleton_append, List.append_nil] at this ⊢
    rw [this]; cases above <;> simp [climb, mk]
  | case3 x above pre y ys below hxy ih =>
    simpa using ih (List.pairwise_cons.mp hs).2
      (fun p hp => by simp at hp; rcases hp with rfl | hp; omega; exact hpre p hp) hb

example : @Zipper.unins_go = @unins_go' := rfl

/-- `Zipper.go_good` by `fun_induction` along `go`. -/
theorem go_good' (x : Nat) (above : Tab) (pre : Row) : ∀ (row : Row) (below : Tab),
    Good above → Sorted (pre.reverse ++ row) → (∀ p ∈ pre, p ≤ x) → Good below →
    Good (go x above pre row below).1 := by
  intro row below ha hs hpre hb
  fun_induction go x above pre row below with
  | case1 x above pre below =>
    intro r hr; simp at hr
    rcases hr with hr | rfl | hr
    · exact ha r hr
    · refine ⟨?_, by simp⟩
      simp only [List.append_nil] at hs
      exact List.pairwise_append.mpr ⟨hs, by simp, by simpa using hpre⟩
    · exact hb r hr
  | case2 x above pre y ys below hxy ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    have hhead : Sorted (below.headD []) := by
      cases below with
      | nil => simp [Sorted]
      | cons r rs => exact (hb r (by simp)).1
    apply ih _ (by simpa using hhead) (by simp) (fun r h => hb r (List.mem_of_mem_tail h))
    intro r hr; simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨?_, by simp⟩
      have hs' := List.pairwise_append.mp hs
      have hyys := List.pairwise_cons.mp hs'.2.1
      refine List.pairwise_append.mpr ⟨hs'.1, ?_, ?_⟩
      · exact List.pairwise_cons.mpr
          ⟨fun b hb' => by have := hyys.1 b hb'; omega, hyys.2⟩
      · intro a ha' b hb'
        simp at hb'
        rcases hb' with rfl | hb'
        · exact hpre a (by simpa using ha')
        · exact hs'.2.2 a ha' b (by simp [hb'])
    · exact ha r hr
  | case3 x above pre y ys below hxy ih =>
    exact ih ha (by simpa using hs)
      (fun p hp => by simp at hp; rcases hp with rfl | hp; omega; exact hpre p hp) hb

example : @Zipper.go_good = @go_good' := rfl

/-- `Zipper.go_eq` (from `RMT.RSK.Semistandard`) by `fun_induction` along `go`. -/
theorem go_eq' (x : Nat) (above : Tab) (pre : Row) : ∀ (row : Row) (below : Tab),
    (∀ p ∈ pre, p ≤ x) →
    go x above pre row below
      = (above.reverse ++ (Nested.ins x ((pre.reverse ++ row) :: below)).1,
         above.length + (Nested.ins x ((pre.reverse ++ row) :: below)).2) := by
  intro row below hp
  fun_induction go x above pre row below with
  | case1 x above pre below =>
    have := Nested.rowIns_append x pre.reverse (by simpa using hp)
    simp [Nested.ins, this]
  | case2 x above pre y ys below hxy ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    rw [ih (by simp)]
    have hr : Nested.rowIns x (pre.reverse ++ y :: ys) = (pre.reverse ++ x :: ys, some y) := by
      rw [rowIns_prefix x (y :: ys) pre.reverse (by simpa using hp)]
      simp [Nested.rowIns, hxy]
    have hb : Nested.ins y (below.headD [] :: below.tail) = Nested.ins y below := by
      cases below <;> simp [Nested.ins, Nested.rowIns]
    simp only [List.reverse_nil, List.nil_append, hb]
    simp only [Nested.ins, hr, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons]
    congr 1
    omega
  | case3 x above pre y ys below hxy ih =>
    rw [ih (fun p hp' => by simp at hp'; rcases hp' with rfl | hp'; omega; exact hp p hp')]
    simp

example : @Zipper.go_eq = @go_eq' := rfl

/-! ## `Zipper`: induction along `up` -/

/-- `Zipper.ins_up` by `fun_induction` along `up`. The four cases are those of `up`:
empty row, swap at the top row, swap below it, skip. -/
theorem ins_up' (y : Nat) : ∀ (above : Tab) (rev done : Row) (below : Tab),
    Sorted (rev.reverse ++ done) → (∃ w ∈ rev, w < y) → Col above (rev.reverse ++ done) →
    ins (up y above rev done below).2 (up y above rev done below).1
      = go y ((rev.reverse ++ done) :: above) [] (below.headD []) below.tail := by
  intro above rev done below hs hex hcol
  -- forward, from where `z` was swapped out: skip the rest of the row, then `z` bumps `y`
  have fwd : ∀ (y z : Nat) (zs done : Row) (below A : Tab),
      Sorted (zs.reverse ++ z :: done) → z < y →
      go z A [] (zs.reverse ++ y :: done) below
        = go y ((zs.reverse ++ z :: done) :: A) [] (below.headD []) below.tail := by
    intro y z zs done below A hs hzy
    have hle : ∀ w ∈ zs.reverse, w ≤ z := fun w hw =>
      (List.pairwise_append.mp hs).2.2 w hw z (by simp)
    rw [go_scan z A below zs.reverse [] (y :: done) hle, go.eq_def]
    simp [hzy]
  fun_induction up y above rev done below with
  | case1 y above done below => obtain ⟨w, hw, _⟩ := hex; simp at hw
  | case2 y z zs done below hzy =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hs ⊢
    exact fwd y z zs done below [] hs hzy
  | case3 y z zs done below hzy a as ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hs hcol ⊢
    obtain ⟨hsa, ⟨w, hwa, hw⟩, hcol'⟩ := hcol
    rw [ih (by simpa using hsa) ⟨w, by simpa using hwa, hw z (by simp)⟩ (by simpa using hcol')]
    simpa using fwd y z zs done below (a :: as) hs hzy
  | case4 y above z zs done below hzy ih =>
    obtain ⟨w, hw, hwy⟩ := hex
    have hw' : w ∈ zs := by
      simp at hw; rcases hw with rfl | h
      · exact absurd hwy hzy
      · exact h
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hs hcol ih ⊢
    exact ih hs ⟨w, hw', hwy⟩ hcol

example : @Zipper.ins_up = @ins_up' := rfl

end Zipper

/-! ## Growth diagrams: induction along `back` -/

namespace Growth

open RMT.RSK.Growth

/-- `Growth.back_grow` by `fun_induction` along `back`. -/
theorem back_grow' (σ : Nat → Nat → Bool) (n : Nat) (hσ : PartialPerm σ) :
    ∀ i j, i ≤ n → j ≤ n →
    back (fun j => grow σ (n + 1) n j) (fun i => grow σ (n + 1) i n) n i j
      = grow σ (n + 1) i j := by
  intro i j hi hj
  fun_induction back (fun j => grow σ (n + 1) n j) (fun i => grow σ (n + 1) i n) n i j with
  | case1 i j h => have : i = n := by omega
                   subst this; rfl
  | case2 i j h h' => have : j = n := by omega
                      subst this; rfl
  | case3 i j h h' ih1 ih2 ih3 =>
    rw [ih1 (by omega) hj, ih2 hi (by omega), ih3 (by omega) (by omega), grow_succ]
    obtain ⟨hμ, hν, hroom, hx⟩ := square_ok σ n hσ i j (by omega)
    rw [bwd_fwd _ _ _ _ (by rw [length_grow]; omega) hμ hν hroom hx]

example : @RMT.RSK.Growth.back_grow = @back_grow' := rfl

end Growth

namespace GrowthGeneric

open RMT.RSK.GrowthGeneric

universe u v

variable {S : Type u} {E : Type v}

/-- `GrowthGeneric.back_grow` by `fun_induction` along `back`. -/
theorem back_grow' (F : Nat → Nat → S → S → S → E → S) (B : Nat → Nat → S → S → S → S × E)
    (z : S) (σ : Nat → Nat → E) (n m : Nat) (h : LocallyInvertible F B z σ n m) :
    ∀ i j, i ≤ n → j ≤ m →
    back B (fun j => grow F z σ n j) (fun i => grow F z σ i m) n m i j = grow F z σ i j := by
  intro i j hi hj
  fun_induction back B (fun j => grow F z σ n j) (fun i => grow F z σ i m) n m i j with
  | case1 i j h' => have : i = n := by omega
                    subst this; rfl
  | case2 i j h₁ h₂ => have : j = m := by omega
                       subst this; rfl
  | case3 i j h₁ h₂ ih1 ih2 ih3 =>
    rw [ih1 (by omega) hj, ih2 hi (by omega), ih3 (by omega) (by omega), h i j (by omega) (by omega)]

example : @RMT.RSK.GrowthGeneric.back_grow.{u, v} = @back_grow'.{u, v} := rfl

/-- `GrowthGeneric.back_congr` by `fun_induction` along the first of the two `back` calls.
The second call is unfolded by hand in each case. -/
theorem back_congr' (B : Nat → Nat → S → S → S → S × E) (n m : Nat)
    (top right top' right' : Nat → S)
    (ht : ∀ j, j ≤ m → top j = top' j) (hr : ∀ i, i ≤ n → right i = right' i) :
    ∀ i j, i ≤ n → j ≤ m → back B top right n m i j = back B top' right' n m i j := by
  intro i j hi hj
  fun_induction back B top right n m i j with
  | case1 i j h => rw [back]; simp [h, ht j hj]
  | case2 i j h₁ h₂ => rw [back]; simp [h₁, h₂, hr i hi]
  | case3 i j h₁ h₂ ih1 ih2 ih3 =>
    rw [back.eq_def B top' right' n m i j]
    simp only [h₁, h₂, ite_false]
    rw [ih1 (by omega) hj, ih2 hi (by omega), ih3 (by omega) (by omega)]

example : @RMT.RSK.GrowthGeneric.back_congr.{u, v} = @back_congr'.{u, v} := rfl

end GrowthGeneric

/-! ## For comparison: the structural `Nested.ins` -/

namespace Nested

open RMT.RSK.Nested

/-- `Nested.unins_ins` by `fun_induction` along the structural `ins`. The `match` on
`rowIns x r` arrives as a hypothesis `hrow`, so no `cases hrow : rowIns x r` is needed. -/
theorem unins_ins' (x : Nat) : ∀ (t : Tab), Good t → unins (ins x t).2 (ins x t).1 = (t, x) := by
  intro t hg
  fun_induction ins x t with
  | case1 x => simp [unins]
  | case2 x r rs r' hrow =>
    have hr := hg r (by simp)
    have happ : r' = r ++ [x] := by
      have := rowIns_none x r (by simp [hrow]); simpa [hrow] using this
    subst happ
    simp [unins, hr.2]
  | case3 x r rs r' y hrow p ih =>
    have hr := hg r (by simp)
    simp only [p, unins]
    rw [ih (fun r' h => hg r' (by simp [h]))]
    simp [rowUnins_rowIns x y r r' hr.1 hrow]

example : @RMT.RSK.Nested.unins_ins = @unins_ins' := rfl

end Nested

end RMT.RSK.FunInd
