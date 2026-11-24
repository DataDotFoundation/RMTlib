import RMTlib.RSK.Nested
import RMTlib.RSK.Zipper

/-!
# RSK as a fold

Level 3 of RSK, the word, is a fold: start from the empty tableau and insert the letters one
at a time, recording one row index per letter. Inverse RSK is the matching unfold: peel the
boxes off one at a time using the recorded indices. This file writes both as folds over
lists, once for every step function, and proves the word-level round trip once.

* `rsk` is `List.foldr` of one insertion step. It equals `Nested.rsk` (right to left).
* `rskl` is `List.foldl` of the same step: ordinary left-to-right RSK. It equals
  `Nested.rsk` of the reversed word.
* `rskRec` is the same function written with the eliminator `List.rec` directly.
* `fold` and `unfold` are generic: `fold step s₀` threads a state through a word and
  collects one output per letter; `unfold unstep` runs the outputs back. `unfold_fold` says
  that if each step is undone by `unstep` on states satisfying an invariant the step keeps,
  then the unfold inverts the fold.

`Nested.unrsk_rsk` and `Zipper.unrsk_rsk` are then instances: plug in the tableau-level
lemmas `unins_ins` and `ins_good` of each version. The word-level induction is not written
again.

## The recursion scheme and what it costs

* Termination: nothing to prove. `List.foldr`, `List.foldl` and `List.rec` are structural.
* Kernel evaluation: `rsk` and `rskl` reduce in the kernel, so `decide` checks concrete
  values (examples below). The step uses `Nested.ins`, itself structural. With
  `Zipper.ins` as the step the fold is still structural, but the step is well-founded and
  does not reduce, so `decide` fails on it.
* `List.rec` and the code generator: the compiler does not support recursors, so `rskRec`
  must be `noncomputable`. The kernel still evaluates it (`decide` works on it too). The
  equation compiler turns `Nested.rsk` into `List.rec` through `List.brecOn`, a
  course-of-values recursor carrying a table of all earlier results; `rskRec` is the
  plain primitive recursion it amounts to here, since `rsk` only ever looks one step back.
  `rskRec_eq` is `rfl` on each constructor.
* Proof shape: the word-level proofs (`fold_inv`, `unfold_fold`) are one induction each,
  for all `step`, `unstep` and invariants. Each instance is a one-liner. The equations
  identifying `Nested.rsk` and `Zipper.rsk` with `fold` are also generic: `fold_unique`
  says any function satisfying the two defining equations of a fold is that fold, and the
  equations hold by `rfl`.
* Statement contortions: `unfold` threads a state from left to right through the recorded
  indices while producing the letters in order, so it is a `foldr` into functions
  `σ → List α` rather than into lists. The round trip needs no condition on the final state.
* Limits: the fold only covers level 3. Levels 1 and 2 (the insertion itself) are
  recursions whose state changes shape (`rowIns` returns a bumped value that is fed to the
  next row), and the invertibility of the step still has to be proved by each version.

## Main results

* `rsk_eq`: `rsk w = Nested.rsk w`. `rskl_eq`: `rskl w = Nested.rsk w.reverse`.
  `rskRec_eq`: `rskRec w = rsk w`.
* `unfold_fold`: a fold whose steps are invertible under a preserved invariant is inverted by
  the unfold.
* `nested_unrsk_rsk`, `zipper_unrsk_rsk`: `unrsk (rsk w) = w` for both bumping versions, as
  instances, with no new induction.
-/

namespace RMT.RSK.Fold

open RMT.RSK

/-! ## Generic folds and unfolds -/

section Generic

variable {α σ ι : Type}

/-- Fold a word right to left through the state, collecting the output of each step. The
first output in the list belongs to the first letter. -/
def fold (step : α → σ → σ × ι) (s₀ : σ) (w : List α) : σ × List ι :=
  w.foldr (fun a p => let q := step a p.1; (q.1, q.2 :: p.2)) (s₀, [])

/-- Run the outputs back from a final state, recovering one letter per output. A `foldr`
into functions of the state, so the state flows from the left while the list is built. -/
def unfold (unstep : ι → σ → σ × α) (s : σ) (is : List ι) : List α :=
  is.foldr (fun i k s => let q := unstep i s; q.2 :: k q.1) (fun _ => []) s

@[simp] theorem fold_nil (step : α → σ → σ × ι) (s₀ : σ) : fold step s₀ [] = (s₀, []) := rfl

@[simp] theorem fold_cons (step : α → σ → σ × ι) (s₀ : σ) (a : α) (w : List α) :
    fold step s₀ (a :: w) =
      ((step a (fold step s₀ w).1).1, (step a (fold step s₀ w).1).2 :: (fold step s₀ w).2) := rfl

@[simp] theorem unfold_nil (unstep : ι → σ → σ × α) (s : σ) : unfold unstep s [] = [] := rfl

@[simp] theorem unfold_cons (unstep : ι → σ → σ × α) (s : σ) (i : ι) (is : List ι) :
    unfold unstep s (i :: is) = (unstep i s).2 :: unfold unstep (unstep i s).1 is := rfl

/-- The invariant holds at the end of a fold if it holds at the start and every step keeps it. -/
theorem fold_inv (step : α → σ → σ × ι) (s₀ : σ) (I : σ → Prop) (h₀ : I s₀)
    (hI : ∀ a s, I s → I (step a s).1) : ∀ w, I (fold step s₀ w).1
  | [] => h₀
  | a :: w => hI a _ (fold_inv step s₀ I h₀ hI w)

/-- **The unfold inverts the fold**, once each step is undone by `unstep` on states where
the invariant holds. The only induction on words in this file. -/
theorem unfold_fold (step : α → σ → σ × ι) (unstep : ι → σ → σ × α) (s₀ : σ) (I : σ → Prop)
    (h₀ : I s₀) (hI : ∀ a s, I s → I (step a s).1)
    (hinv : ∀ a s, I s → unstep (step a s).2 (step a s).1 = (s, a)) :
    ∀ w, unfold unstep (fold step s₀ w).1 (fold step s₀ w).2 = w
  | [] => rfl
  | a :: w => by
    rw [fold_cons, unfold_cons, hinv a _ (fold_inv step s₀ I h₀ hI w),
      unfold_fold step unstep s₀ I h₀ hI hinv w]

/-- Any function satisfying the two defining equations of `fold step s₀` is that fold. -/
theorem fold_unique (step : α → σ → σ × ι) (s₀ : σ) (f : List α → σ × List ι)
    (h0 : f [] = (s₀, []))
    (h1 : ∀ a w, f (a :: w) = ((step a (f w).1).1, (step a (f w).1).2 :: (f w).2)) :
    ∀ w, f w = fold step s₀ w
  | [] => h0
  | a :: w => by rw [h1, fold_unique step s₀ f h0 h1 w]; rfl

/-- Any function satisfying the two defining equations of `unfold unstep` is that unfold. -/
theorem unfold_unique (unstep : ι → σ → σ × α) (g : σ → List ι → List α)
    (h0 : ∀ s, g s [] = []) (h1 : ∀ s i is, g s (i :: is) = (unstep i s).2 :: g (unstep i s).1 is) :
    ∀ s is, g s is = unfold unstep s is
  | s, [] => h0 s
  | s, i :: is => by rw [h1, unfold_unique unstep g h0 h1 _ is]; rfl

end Generic

/-! ## RSK as `foldr`, `foldl` and `List.rec` -/

/-- One RSK step: insert `x` into the tableau and record the row of the new box. -/
def step (x : Nat) (p : Tab × List Nat) : Tab × List Nat :=
  let q := Nested.ins x p.1; (q.1, q.2 :: p.2)

/-- RSK as `List.foldr`: the letters are inserted right to left, as in `Nested.rsk`. -/
def rsk (w : List Nat) : Tab × List Nat := w.foldr step ([], [])

/-- Ordinary left-to-right RSK as `List.foldl`. The recording data comes out in reverse
order: its head is the row of the last box added. -/
def rskl (w : List Nat) : Tab × List Nat := w.foldl (fun p x => step x p) ([], [])

/-- RSK with the eliminator `List.rec` directly, with no equation compiler. The code
generator does not support recursors, hence `noncomputable`; the kernel still reduces it. -/
noncomputable def rskRec (w : List Nat) : Tab × List Nat :=
  List.rec (motive := fun _ => Tab × List Nat) ([], []) (fun x _ ih => step x ih) w

theorem rsk_eq : ∀ w, rsk w = Nested.rsk w
  | [] => rfl
  | x :: w => by
    show step x (rsk w) = _
    rw [rsk_eq w]; rfl

theorem rskl_eq (w : List Nat) : rskl w = Nested.rsk w.reverse := by
  rw [← rsk_eq, rsk, List.foldr_reverse]; rfl

theorem rskRec_eq : ∀ w, rskRec w = rsk w
  | [] => rfl
  | x :: w => by
    show step x (rskRec w) = step x (rsk w)
    rw [rskRec_eq w]

/-- `rsk` is the generic fold with `Nested.ins` as the step (definitionally). -/
theorem rsk_eq_fold (w : List Nat) : rsk w = fold Nested.ins [] w := rfl

/-! ## The round trip for both bumping versions, as instances -/

/-- `Nested.rsk` is a fold. -/
theorem nested_rsk_eq_fold : ∀ w, Nested.rsk w = fold Nested.ins [] w :=
  fold_unique _ _ _ rfl (fun _ _ => rfl)

/-- `Nested.unrsk` is an unfold. -/
theorem nested_unrsk_eq_unfold : ∀ t is, Nested.unrsk t is = unfold Nested.unins t is :=
  unfold_unique _ _ (fun _ => rfl) (fun _ _ _ => rfl)

/-- `Zipper.rsk` is a fold. -/
theorem zipper_rsk_eq_fold : ∀ w, Zipper.rsk w = fold Zipper.ins [] w :=
  fold_unique _ _ _ rfl (fun _ _ => rfl)

/-- `Zipper.unrsk` is an unfold. -/
theorem zipper_unrsk_eq_unfold : ∀ t is, Zipper.unrsk t is = unfold Zipper.unins t is :=
  unfold_unique _ _ (fun _ => rfl) (fun _ _ _ => rfl)

/-- `Nested.unrsk_rsk` as an instance of `unfold_fold`. -/
theorem nested_unrsk_rsk (w : List Nat) : Nested.unrsk (Nested.rsk w).1 (Nested.rsk w).2 = w := by
  rw [nested_rsk_eq_fold, nested_unrsk_eq_unfold]
  exact unfold_fold _ _ _ Good (by simp [Good]) Nested.ins_good Nested.unins_ins w

/-- `Zipper.unrsk_rsk` as an instance of `unfold_fold`: the same proof, other step lemmas. -/
theorem zipper_unrsk_rsk (w : List Nat) : Zipper.unrsk (Zipper.rsk w).1 (Zipper.rsk w).2 = w := by
  rw [zipper_rsk_eq_fold, zipper_unrsk_eq_unfold]
  exact unfold_fold _ _ _ Good (by simp [Good]) Zipper.ins_good Zipper.unins_ins w

/-- Left-to-right RSK is inverted by unfolding and reversing. -/
theorem unrsk_rskl (w : List Nat) : (Nested.unrsk (rskl w).1 (rskl w).2).reverse = w := by
  rw [rskl_eq, Nested.unrsk_rsk, List.reverse_reverse]

/-! ## The kernel evaluates the fold -/

example : rsk [3, 1, 2] = ([[1, 3], [2]], [0, 1, 0]) := by decide
example : rskl [2, 1, 3] = ([[1, 3], [2]], [0, 1, 0]) := by decide
example : rsk [2, 4, 1, 3, 1] = ([[1, 1, 2], [3, 4]], [1, 0, 1, 0, 0]) := by decide
example : rskRec [3, 1, 2] = ([[1, 3], [2]], [0, 1, 0]) := by decide

end RMT.RSK.Fold
