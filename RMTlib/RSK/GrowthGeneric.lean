import RMTlib.RSK.Growth

/-!
# Growth diagrams for any local rule

`RMT.RSK.Growth` fills a grid with Fomin's local rule for partial permutations and proves
that the grid can be run backwards. Only one part of that argument depends on the rule: the
local theorem `bwd_fwd`, that the backward rule undoes the forward rule on every square that
occurs. This file writes the rest once, for any local rule.

The rule may depend on the square `(i, j)`. This is what a growth diagram whose rows and
columns carry labels (a parity, say) needs: each square uses the rule of its labels.

* `grow F z σ i j`: the forward grid, from the bottom-left corner, with boundary `z`.
* `back B top right n m i j`: the backward grid of an `n × m` rectangle, from the top-right
  corner, using only the top edge `top j = λ(n, j)` and the right edge `right i = λ(i, m)`.
* `LocallyInvertible`: on every square of the rectangle, `B` undoes `F`.

## Main results

* `back_grow`, `backEntry_grow`: if `B` undoes `F` on every square, the backward grid rebuilds
  the forward grid and every entry of the filling from the two outer edges.
* `eq_of_edges`: two fillings with the same outer edges are equal, if both are locally
  invertible. This is injectivity of the growth-diagram correspondence.
* `RMT.RSK.Growth` is an instance (`Growth.grow_eq`, `Growth.locallyInvertible`).

Mathlib-free.
-/

namespace RMT.RSK.GrowthGeneric

universe u v

variable {S : Type u} {E : Type v}

/-- The forward growth diagram of `σ` for the local rule `F`, filled from the bottom-left
corner, with every boundary shape equal to `z`. `F i j ρ μ ν x` is the shape at `(i+1, j+1)`
from those at `(i, j)`, `(i+1, j)`, `(i, j+1)` and the entry `x = σ i j`. -/
def grow (F : Nat → Nat → S → S → S → E → S) (z : S) (σ : Nat → Nat → E) :
    Nat → Nat → S
  | 0, _ => z
  | _, 0 => z
  | i + 1, j + 1 =>
    F i j (grow F z σ i j) (grow F z σ (i + 1) j) (grow F z σ i (j + 1)) (σ i j)
termination_by i j => (i, j)

/-- The backward growth diagram of an `n × m` rectangle, filled from the top-right corner using
only the top edge `top j = λ(n, j)` and the right edge `right i = λ(i, m)`. `B i j μ ν λ`
returns the shape at `(i, j)` and the entry of square `(i, j)`. -/
def back (B : Nat → Nat → S → S → S → S × E) (top right : Nat → S) (n m : Nat) (i j : Nat) : S :=
  if n ≤ i then top j
  else if m ≤ j then right i
  else (B i j (back B top right n m (i + 1) j) (back B top right n m i (j + 1))
            (back B top right n m (i + 1) (j + 1))).1
termination_by (n - i, m - j)
decreasing_by all_goals (simp [Prod.lex_def]; omega)

/-- The entry of square `(i, j)` recovered by the backward grid. -/
def backEntry (B : Nat → Nat → S → S → S → S × E) (top right : Nat → S) (n m i j : Nat) : E :=
  (B i j (back B top right n m (i + 1) j) (back B top right n m i (j + 1))
       (back B top right n m (i + 1) (j + 1))).2

section Grid

variable (F : Nat → Nat → S → S → S → E → S) (B : Nat → Nat → S → S → S → S × E)
  (z : S) (σ : Nat → Nat → E)

theorem grow_zero_left (j : Nat) : grow F z σ 0 j = z := by simp [grow]

theorem grow_zero_right (i : Nat) : grow F z σ i 0 = z := by cases i <;> simp [grow]

theorem grow_succ (i j : Nat) : grow F z σ (i + 1) (j + 1)
    = F i j (grow F z σ i j) (grow F z σ (i + 1) j) (grow F z σ i (j + 1)) (σ i j) := by
  rw [grow]

/-- On every square of the `n × m` rectangle, the backward rule undoes the forward rule. -/
def LocallyInvertible (n m : Nat) : Prop :=
  ∀ i j, i < n → j < m →
    B i j (grow F z σ (i + 1) j) (grow F z σ i (j + 1)) (grow F z σ (i + 1) (j + 1))
      = (grow F z σ i j, σ i j)

/-- **The backward grid rebuilds the forward grid** from its top and right edges. -/
theorem back_grow (n m : Nat) (h : LocallyInvertible F B z σ n m) : ∀ i j, i ≤ n → j ≤ m →
    back B (fun j => grow F z σ n j) (fun i => grow F z σ i m) n m i j = grow F z σ i j
  | i, j, hi, hj => by
    rw [back]
    split
    · have : i = n := by omega
      subst this; rfl
    · split
      · have : j = m := by omega
        subst this; rfl
      · rw [back_grow n m h (i + 1) j (by omega) hj, back_grow n m h i (j + 1) hi (by omega),
          back_grow n m h (i + 1) (j + 1) (by omega) (by omega), h i j (by omega) (by omega)]
termination_by i j => (n - i, m - j)

/-- **The backward grid recovers every entry** of the filling. -/
theorem backEntry_grow (n m : Nat) (h : LocallyInvertible F B z σ n m) (i j : Nat)
    (hi : i < n) (hj : j < m) :
    backEntry B (fun j => grow F z σ n j) (fun i => grow F z σ i m) n m i j = σ i j := by
  unfold backEntry
  rw [back_grow F B z σ n m h (i + 1) j (by omega) (by omega),
    back_grow F B z σ n m h i (j + 1) (by omega) (by omega),
    back_grow F B z σ n m h (i + 1) (j + 1) (by omega) (by omega), h i j hi hj]

/-- The backward grid inside the rectangle depends only on the edges inside it. -/
theorem back_congr (n m : Nat) (top right top' right' : Nat → S)
    (ht : ∀ j, j ≤ m → top j = top' j) (hr : ∀ i, i ≤ n → right i = right' i) :
    ∀ i j, i ≤ n → j ≤ m → back B top right n m i j = back B top' right' n m i j
  | i, j, hi, hj => by
    rw [back.eq_def B top right n m i j, back.eq_def B top' right' n m i j]
    split
    · exact ht j hj
    · split
      · exact hr i hi
      · rw [back_congr n m top right top' right' ht hr (i + 1) j (by omega) hj,
          back_congr n m top right top' right' ht hr i (j + 1) hi (by omega),
          back_congr n m top right top' right' ht hr (i + 1) (j + 1) (by omega) (by omega)]
termination_by i j => (n - i, m - j)

/-- **Injectivity.** Two locally invertible fillings of an `n × m` rectangle with the same top
and right edges agree on the rectangle. -/
theorem eq_of_edges (τ : Nat → Nat → E) (n m : Nat) (hσ : LocallyInvertible F B z σ n m)
    (hτ : LocallyInvertible F B z τ n m)
    (htop : ∀ j, j ≤ m → grow F z σ n j = grow F z τ n j)
    (hright : ∀ i, i ≤ n → grow F z σ i m = grow F z τ i m) :
    ∀ i j, i < n → j < m → σ i j = τ i j := by
  intro i j hi hj
  rw [← backEntry_grow F B z σ n m hσ i j hi hj, ← backEntry_grow F B z τ n m hτ i j hi hj]
  unfold backEntry
  have hb := back_congr B n m _ _ _ _ htop hright
  rw [hb (i + 1) j (by omega) (by omega), hb i (j + 1) (by omega) (by omega),
    hb (i + 1) (j + 1) (by omega) (by omega)]

end Grid

/-! ## Fomin's rule for partial permutations is an instance -/

namespace Growth

open RMT.RSK.Growth

/-- `RMT.RSK.Growth.grow` is the generic grid for Fomin's rule, the same at every square. -/
theorem grow_eq (σ : Nat → Nat → Bool) (N : Nat) : ∀ i j,
    RMT.RSK.Growth.grow σ N i j = GrowthGeneric.grow (fun _ _ => fwd) (zeros N) σ i j
  | 0, j => by rw [RMT.RSK.Growth.grow_zero_left, GrowthGeneric.grow_zero_left]
  | i + 1, 0 => by rw [RMT.RSK.Growth.grow_zero_right, GrowthGeneric.grow_zero_right]
  | i + 1, j + 1 => by
    rw [RMT.RSK.Growth.grow_succ, GrowthGeneric.grow_succ, grow_eq σ N i j,
      grow_eq σ N (i + 1) j, grow_eq σ N i (j + 1)]
termination_by i j => (i, j)

/-- For a partial permutation, Fomin's rule is locally invertible on the `n × n` square. -/
theorem locallyInvertible (σ : Nat → Nat → Bool) (n : Nat) (hσ : PartialPerm σ) :
    LocallyInvertible (fun _ _ => fwd) (fun _ _ => bwd) (zeros (n + 1)) σ n n := by
  intro i j _ hj
  obtain ⟨hμ, hν, hroom, hx⟩ := square_ok σ n hσ i j hj
  simp only [← grow_eq]
  rw [RMT.RSK.Growth.grow_succ]
  exact bwd_fwd _ _ _ _ (by rw [length_grow]; omega) hμ hν hroom hx

end Growth

end RMT.RSK.GrowthGeneric
