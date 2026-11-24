import RMTlib.RSK.GrowthGeneric

/-!
# The bosonic local rule: growth diagrams for fillings with entries in `ℕ`

Fomin's local rule for RSK on fillings with entries in `ℕ` (Fomin 1995; Krattenthaler,
*Growth diagrams, and increasing and decreasing chains in fillings of Ferrers shapes*, 2006).
With `ρ, μ, ν` the shapes at the bottom-left, bottom-right and top-left of a square and `x` its
entry, the top-right shape `λ` is, row by row,

    λ₀ = max μ₀ ν₀ + x,      λ_{a+1} = max μ_{a+1} ν_{a+1} + (min μ_a ν_a − ρ_a).

The second term is a *carry*: what both sides added to row `a` beyond `ρ` is pushed into row
`a + 1`, and the entry `x` is pushed into row `0`. This is the bosonic half of the symmetry
between bosons and fermions (Cauchy kernel `∏ 1/(1 − x_i y_j)`, row insertion).

The backward rule reads the carries back from the bottom row up:
`c_a = λ_a − max μ_a ν_a`, then `ρ_a = min μ_a ν_a − c_{a+1}` and `x = c_0`.

Shapes are vectors of fixed length padded with zeros (`RMT.RSK.Growth.Part`), as in
`RMT.RSK.Growth`.

## Main results

* `bwd_fwd`: the backward rule undoes the forward rule on every square with `ρ ≤ μ` and `ρ ≤ ν`
  (entrywise) whose carry out of the last row is zero. Unlike Fomin's rule for permutations,
  no strip condition is needed for invertibility.
* `locallyInvertible`: every filling of an `n × m` rectangle with entries in `ℕ` is locally
  invertible when shapes have `m + 1` rows.
* `eq_of_edges`: a filling is determined by the top and right edges of its growth diagram.

Mathlib-free.
-/

namespace RMT.RSK.GrowthKnuth

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthGeneric (grow grow_zero_left grow_zero_right grow_succ LocallyInvertible)

/-- The forward rule with an incoming carry `c` into the first row. -/
def fwdC : Nat → Part → Part → Part → Part
  | c, r :: ρ, a :: μ, b :: ν => (max a b + c) :: fwdC (min a b - r) ρ μ ν
  | _, _, _, _ => []

/-- The carry out of the last row. -/
def carryOut : Nat → Part → Part → Part → Nat
  | _, r :: ρ, a :: μ, b :: ν => carryOut (min a b - r) ρ μ ν
  | c, _, _, _ => c

/-- The backward rule: the shape `ρ` and the carry into the first row (the entry). -/
def bwdC : Part → Part → Part → Part × Nat
  | a :: μ, b :: ν, l :: lam =>
    let p := bwdC μ ν lam
    ((min a b - p.2) :: p.1, l - max a b)
  | _, _, _ => ([], 0)

/-- The forward local rule: `ρ` bottom-left, `μ` bottom-right, `ν` top-left, `x` the entry. -/
def fwd (ρ μ ν : Part) (x : Nat) : Part := fwdC x ρ μ ν

/-- The backward local rule: from `μ`, `ν` and the top-right corner, recover `ρ` and `x`. -/
def bwd (μ ν lam : Part) : Part × Nat := bwdC μ ν lam

/-- Entrywise `≤` between shapes of the same length. -/
def Le : Part → Part → Prop
  | [], [] => True
  | a :: l, b :: m => a ≤ b ∧ Le l m
  | _, _ => False

/-! ## The local theorem -/

theorem Le.length_eq : ∀ {l m : Part}, Le l m → l.length = m.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Le.length_eq h.2]

theorem Le.refl : ∀ l : Part, Le l l
  | [] => trivial
  | _ :: l => ⟨Nat.le_refl _, Le.refl l⟩

/-- **The local theorem.** If `ρ ≤ μ`, `ρ ≤ ν` entrywise and nothing is carried out of the last
row, the backward rule recovers `ρ` and the incoming carry. -/
theorem bwdC_fwdC : ∀ (c : Nat) (ρ μ ν : Part), Le ρ μ → Le ρ ν → carryOut c ρ μ ν = 0 →
    bwdC μ ν (fwdC c ρ μ ν) = (ρ, c)
  | c, [], [], [], _, _, h => by simp [carryOut] at h; simp [bwdC, h]
  | c, r :: ρ, a :: μ, b :: ν, ⟨ha, hμ⟩, ⟨hb, hν⟩, h => by
    simp only [carryOut] at h
    simp only [fwdC, bwdC, bwdC_fwdC (min a b - r) ρ μ ν hμ hν h]
    congr 2 <;> omega

/-- `bwd_fwd`: the local rule is invertible on every square with `ρ ≤ μ`, `ρ ≤ ν` and no carry
out of the last row. -/
theorem bwd_fwd (ρ μ ν : Part) (x : Nat) (hμ : Le ρ μ) (hν : Le ρ ν)
    (h : carryOut x ρ μ ν = 0) : bwd μ ν (fwd ρ μ ν x) = (ρ, x) :=
  bwdC_fwdC x ρ μ ν hμ hν h

theorem length_fwdC : ∀ (c : Nat) (ρ μ ν : Part), ρ.length = μ.length → μ.length = ν.length →
    (fwdC c ρ μ ν).length = μ.length
  | _, [], [], [], _, _ => rfl
  | _, _ :: ρ, _ :: μ, _ :: ν, h1, h2 => by
    simp only [fwdC, List.length_cons]
    rw [length_fwdC _ ρ μ ν (by simpa using h1) (by simpa using h2)]
  | _, [], _ :: _, _, h1, _ => by simp at h1
  | _, _ :: _, [], _, h1, _ => by simp at h1
  | _, _ :: _, _ :: _, [], _, h2 => by simp at h2
  | _, [], [], _ :: _, _, h2 => by simp at h2

theorem le_fwdC_left : ∀ (c : Nat) (ρ μ ν : Part), ρ.length = μ.length → μ.length = ν.length →
    Le μ (fwdC c ρ μ ν)
  | _, [], [], [], _, _ => trivial
  | _, _ :: ρ, _ :: μ, _ :: ν, h1, h2 =>
    ⟨by omega, le_fwdC_left _ ρ μ ν (by simpa using h1) (by simpa using h2)⟩
  | _, [], _ :: _, _, h1, _ => by simp at h1
  | _, _ :: _, [], _, h1, _ => by simp at h1
  | _, _ :: _, _ :: _, [], _, h2 => by simp at h2
  | _, [], [], _ :: _, _, h2 => by simp at h2

theorem le_fwdC_right : ∀ (c : Nat) (ρ μ ν : Part), ρ.length = μ.length → μ.length = ν.length →
    Le ν (fwdC c ρ μ ν)
  | _, [], [], [], _, _ => trivial
  | _, _ :: ρ, _ :: μ, _ :: ν, h1, h2 =>
    ⟨by omega, le_fwdC_right _ ρ μ ν (by simpa using h1) (by simpa using h2)⟩
  | _, [], _ :: _, _, h1, _ => by simp at h1
  | _, _ :: _, [], _, h1, _ => by simp at h1
  | _, _ :: _, _ :: _, [], _, h2 => by simp at h2
  | _, [], [], _ :: _, _, h2 => by simp at h2

/-- No carry leaves the last row if the last row of `μ` is empty. -/
theorem carryOut_eq_zero : ∀ (c : Nat) (ρ μ ν : Part), ρ.length = μ.length →
    μ.length = ν.length → 0 < μ.length → μ.getD (μ.length - 1) 0 = 0 → carryOut c ρ μ ν = 0
  | _, [_], [a], [_], _, _, _, h => by simp at h; simp [carryOut, carryOut, h]
  | c, r :: r' :: ρ, a :: a' :: μ, b :: b' :: ν, h1, h2, _, h => by
    show carryOut (min a b - r) (r' :: ρ) (a' :: μ) (b' :: ν) = 0
    exact carryOut_eq_zero _ (r' :: ρ) (a' :: μ) (b' :: ν) (by simpa using h1) (by simpa using h2)
      (by simp) (by simpa using h)
  | _, [], [], [], _, _, h0, _ => by simp at h0
  | _, [], _ :: _, _, h1, _, _, _ => by simp at h1
  | _, _ :: _, [], _, h1, _, _, _ => by simp at h1
  | _, _ :: _, _ :: _, [], _, h2, _, _ => by simp at h2
  | _, [], [], _ :: _, _, h2, _, _ => by simp at h2
  | _, [_], [_], _ :: _ :: _, _, h2, _, _ => by simp at h2
  | _, [_], _ :: _ :: _, _, h1, _, _, _ => by simp at h1
  | _, _ :: _ :: _, [_], _, h1, _, _, _ => by simp at h1
  | _, _ :: _ :: _, _ :: _ :: _, [_], _, h2, _, _ => by simp at h2

/-- A row of the result is empty if that row of `μ` and of `ν` is empty and nothing is carried
into it. -/
theorem getD_fwdC_eq_zero : ∀ (k c : Nat) (ρ μ ν : Part), μ.getD k 0 = 0 → ν.getD k 0 = 0 →
    (match k with
      | 0 => c = 0
      | k' + 1 => min (μ.getD k' 0) (ν.getD k' 0) - ρ.getD k' 0 = 0) →
    (fwdC c ρ μ ν).getD k 0 = 0
  | 0, c, _ :: _, a :: _, b :: _, hμ, hν, hc => by
    simp only [List.getD_cons_zero] at hμ hν
    simp [fwdC, hμ, hν, hc]
  | k + 1, c, r :: ρ, a :: μ, b :: ν, hμ, hν, hc => by
    simp only [List.getD_cons_succ] at hμ hν
    simp only [fwdC, List.getD_cons_succ]
    refine getD_fwdC_eq_zero k _ ρ μ ν hμ hν ?_
    cases k with
    | zero => simpa using hc
    | succ k => simpa using hc
  | _, _, [], _, _, _, _, _ => by simp [fwdC]
  | _, _, _ :: _, [], _, _, _, _ => by simp [fwdC]
  | _, _, _ :: _, _ :: _, [], _, _, _ => by simp [fwdC]

/-! ## The grid -/

/-- The forward rule at every square. -/
abbrev F : Nat → Nat → Part → Part → Part → Nat → Part := fun _ _ => fwd

/-- The backward rule at every square. -/
abbrev B : Nat → Nat → Part → Part → Part → Part × Nat := fun _ _ => bwd

section Grid

variable (σ : Nat → Nat → Nat) (N : Nat)

theorem getD_zeros (a : Nat) : (zeros N).getD a 0 = 0 := by
  simp [zeros, List.getElem?_replicate]; split <;> rfl

theorem length_grow : ∀ i j, (grow F (zeros N) σ i j).length = N
  | 0, j => by simp [grow_zero_left, zeros]
  | i + 1, 0 => by simp [grow_zero_right, zeros]
  | i + 1, j + 1 => by
    rw [grow_succ]
    simp only [F, fwd]
    rw [length_fwdC _ _ _ _ (by rw [length_grow i j, length_grow (i + 1) j])
      (by rw [length_grow (i + 1) j, length_grow i (j + 1)]), length_grow (i + 1) j]
termination_by i j => (i, j)

/-- The shape grows from each row of the grid to the next. -/
theorem le_succ_row (i j : Nat) : Le (grow F (zeros N) σ i j) (grow F (zeros N) σ (i + 1) j) := by
  cases j with
  | zero => rw [grow_zero_right, grow_zero_right]; exact Le.refl _
  | succ j =>
    rw [grow_succ]
    exact le_fwdC_right _ _ _ _ (by rw [length_grow, length_grow]) (by rw [length_grow, length_grow])

/-- The shape grows from each column of the grid to the next. -/
theorem le_succ_col (i j : Nat) : Le (grow F (zeros N) σ i j) (grow F (zeros N) σ i (j + 1)) := by
  cases i with
  | zero => rw [grow_zero_left, grow_zero_left]; exact Le.refl _
  | succ i =>
    rw [grow_succ]
    exact le_fwdC_left _ _ _ _ (by rw [length_grow, length_grow]) (by rw [length_grow, length_grow])

/-- The shape at `(i, j)` has no boxes in rows `≥ j`. -/
theorem supp_grow : ∀ i j a, j ≤ a → (grow F (zeros N) σ i j).getD a 0 = 0
  | 0, j, a, _ => by rw [grow_zero_left]; exact getD_zeros N a
  | i + 1, 0, a, _ => by rw [grow_zero_right]; exact getD_zeros N a
  | i + 1, j + 1, a, ha => by
    rw [grow_succ]
    refine getD_fwdC_eq_zero a _ _ _ _ (supp_grow (i + 1) j a (by omega))
      (supp_grow i (j + 1) a ha) ?_
    cases a with
    | zero => omega
    | succ a =>
      show min _ _ - _ = 0
      rw [supp_grow (i + 1) j a (by omega)]
      simp
termination_by i j => (i, j)

/-- **Every filling with entries in `ℕ` is locally invertible** on an `n × m` rectangle, when
shapes have `m + 1` rows. -/
theorem locallyInvertible (n m : Nat) :
    LocallyInvertible F B (zeros (m + 1)) σ n m := by
  intro i j _ hj
  simp only [B]
  rw [grow_succ]
  refine bwd_fwd _ _ _ _ (le_succ_row σ _ i j) (le_succ_col σ _ i j) ?_
  refine carryOut_eq_zero _ _ _ _ (by rw [length_grow, length_grow])
    (by rw [length_grow, length_grow]) (by rw [length_grow]; omega) ?_
  rw [length_grow]
  exact supp_grow σ _ (i + 1) j _ (by omega)

/-- **A filling with entries in `ℕ` is determined by the outer edges of its growth diagram.** -/
theorem eq_of_edges (τ : Nat → Nat → Nat) (n m : Nat)
    (htop : ∀ j, j ≤ m → grow F (zeros (m + 1)) σ n j = grow F (zeros (m + 1)) τ n j)
    (hright : ∀ i, i ≤ n → grow F (zeros (m + 1)) σ i m = grow F (zeros (m + 1)) τ i m) :
    ∀ i j, i < n → j < m → σ i j = τ i j :=
  GrowthGeneric.eq_of_edges F B _ σ τ n m (locallyInvertible σ n m) (locallyInvertible τ n m)
    htop hright

end Grid

end RMT.RSK.GrowthKnuth
