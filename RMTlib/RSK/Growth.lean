/-!
# RSK by Fomin growth diagrams: a recursion over a grid

A partial permutation (at most one `1` in each row and column of a 0/1 matrix `σ`) is
turned into a grid of shapes `λ(i,j)` by ONE recursion over two indices:

    λ(0,j) = λ(i,0) = ∅,    λ(i+1,j+1) = fwd λ(i,j) λ(i+1,j) λ(i,j+1) (σ i j)

where `fwd` is Fomin's local rule. The recursion makes three calls and is well-founded for
the lexicographic order on `(i, j)`. The top edge `λ(n,·)` gives P and the right edge
`λ(·,n)` gives Q.

The inverse `back` fills the grid from the top-right corner using only those two edges,
by the mirrored recursion with measure `(n - i, n - j)`, and recovers each entry of `σ`.

All of the invertibility sits in ONE square: `bwd_fwd` says the backward local rule undoes
the forward one. The global theorems `back_grow` and `backEntry_grow` apply it at every
square, using the invariants `SquareOK` proved by the forward recursion.

Shapes are vectors of fixed length padded with zeros, so equality is list equality and every
operation is entrywise.

## Main results

* `bwd_fwd`: the local rule is invertible on every square that can occur.
* `square_ok`: every square of the forward grid of a partial permutation is such a square.
* `back_grow`, `backEntry_grow`: the backward grid rebuilds the forward grid and the matrix.
* `unrskGrowth_rskGrowth`: inverse RSK recovers every permutation of `{0, …, n-1}`.
-/

namespace RMT.RSK.Growth

/-- A shape, as a vector of row lengths padded with zeros. -/
abbrev Part := List Nat

/-- Add a box in row `k`. -/
def bump : Nat → Part → Part
  | _, [] => []
  | 0, a :: l => (a + 1) :: l
  | k + 1, a :: l => a :: bump k l

/-- Remove a box from row `k`. -/
def unbump : Nat → Part → Part
  | _, [] => []
  | 0, a :: l => (a - 1) :: l
  | k + 1, a :: l => a :: unbump k l

/-- The first row in which two shapes differ. -/
def firstDiff : Part → Part → Nat
  | a :: l, b :: m => if a = b then firstDiff l m + 1 else 0
  | _, _ => 0

/-- Entrywise maximum (the union of two shapes). -/
def pmax : Part → Part → Part
  | a :: l, b :: m => max a b :: pmax l m
  | _, _ => []

/-- Entrywise minimum (the intersection of two shapes). -/
def pmin : Part → Part → Part
  | a :: l, b :: m => min a b :: pmin l m
  | _, _ => []

/-- Fomin's local rule. `ρ` is the bottom-left corner of a square, `μ` the bottom-right,
`ν` the top-left and `x` the matrix entry; the result is the top-right corner. -/
def fwd (ρ μ ν : Part) (x : Bool) : Part :=
  if μ ≠ ν then pmax μ ν                                  -- grew in different rows: union
  else if μ = ρ then (if x then bump 0 ρ else ρ)           -- nothing grew: a 1 starts row 0
  else bump (firstDiff μ ρ + 1) μ                          -- both grew in row k: push to k+1

/-- The local rule backwards: from `μ`, `ν` and the top-right corner, recover `ρ` and `x`. -/
def bwd (μ ν lam : Part) : Part × Bool :=
  if μ ≠ ν then (pmin μ ν, false)
  else if lam = μ then (μ, false)
  else
    let k := firstDiff lam μ
    if k = 0 then (μ, true) else (unbump (k - 1) μ, false)

/-! ## Lemmas about single shapes (plain inductions) -/

theorem length_bump : ∀ k (l : Part), (bump k l).length = l.length
  | k, [] => by cases k <;> rfl
  | 0, _ :: _ => rfl
  | k + 1, _ :: l => by simp [bump, length_bump k l]

theorem length_pmax : ∀ (l m : Part), (pmax l m).length = min l.length m.length
  | [], _ => by simp [pmax]
  | _ :: _, [] => by simp [pmax]
  | _ :: l, _ :: m => by simp [pmax, length_pmax l m, Nat.min_def]; split <;> omega

theorem unbump_bump : ∀ k (l : Part), unbump k (bump k l) = l
  | k, [] => by cases k <;> rfl
  | 0, _ :: _ => by simp [bump, unbump]
  | k + 1, _ :: l => by simp [bump, unbump, unbump_bump k l]

theorem bump_comm : ∀ a b (l : Part), bump a (bump b l) = bump b (bump a l)
  | a, b, [] => by cases a <;> cases b <;> rfl
  | 0, 0, _ :: _ => rfl
  | 0, _ + 1, _ :: _ => rfl
  | _ + 1, 0, _ :: _ => rfl
  | a + 1, b + 1, _ :: l => by simp [bump, bump_comm a b l]

theorem firstDiff_self : ∀ l : Part, firstDiff l l = l.length
  | [] => rfl
  | _ :: l => by simp [firstDiff, firstDiff_self l]

theorem firstDiff_bump : ∀ k (l : Part), k < l.length → firstDiff (bump k l) l = k
  | _, [], h => by simp at h
  | 0, _ :: _, _ => by simp [bump, firstDiff]
  | k + 1, _ :: l, h => by
    simp [bump, firstDiff, firstDiff_bump k l (by simp at h; omega)]

/-- Two different shapes of the same length differ at `firstDiff`. -/
theorem firstDiff_spec : ∀ (l m : Part), l.length = m.length → l ≠ m →
    firstDiff l m < l.length ∧ l.getD (firstDiff l m) 0 ≠ m.getD (firstDiff l m) 0
  | [], [], _, h => absurd rfl h
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: m, hl, hne => by
    by_cases hab : a = b
    · subst hab
      have hne' : l ≠ m := fun e => hne (by rw [e])
      have := firstDiff_spec l m (by simpa using hl) hne'
      have e : firstDiff (a :: l) (a :: m) = firstDiff l m + 1 := by simp [firstDiff]
      rw [e, List.getD_cons_succ, List.getD_cons_succ, List.length_cons]
      exact ⟨by omega, this.2⟩
    · simp [firstDiff, hab]

theorem bump_ne {k} {l : Part} (h : k < l.length) : bump k l ≠ l := by
  intro e
  have := firstDiff_bump k l h
  rw [e, firstDiff_self] at this
  omega

theorem bump_ne_bump {a b} {l : Part} (ha : a < l.length) (hb : b < l.length) (hab : a ≠ b) :
    bump a l ≠ bump b l := by
  intro e
  have h1 := firstDiff_bump a l ha
  rw [e, firstDiff_bump b l hb] at h1
  exact hab h1.symm

theorem getD_bump_self : ∀ a (l : Part), a < l.length → (bump a l).getD a 0 = l.getD a 0 + 1
  | _, [], h => by simp at h
  | 0, _ :: _, _ => by simp [bump]
  | a + 1, _ :: l, h => by
    simp only [bump, List.getD_cons_succ]; exact getD_bump_self a l (by simp at h; omega)

theorem getD_bump_ne : ∀ a b (l : Part), b ≠ a → (bump a l).getD b 0 = l.getD b 0
  | a, _, [], _ => by cases a <;> rfl
  | 0, 0, _ :: _, h => absurd rfl h
  | 0, _ + 1, _ :: _, _ => by simp [bump]
  | _ + 1, 0, _ :: _, _ => by simp [bump]
  | a + 1, b + 1, _ :: l, h => by
    simp only [bump, List.getD_cons_succ]; exact getD_bump_ne a b l (by omega)

theorem getD_pmax_zero : ∀ (l m : Part) a, l.getD a 0 = 0 → m.getD a 0 = 0 →
    (pmax l m).getD a 0 = 0
  | [], _, _, _, _ => by simp [pmax]
  | _ :: _, [], _, _, _ => by simp [pmax]
  | _ :: _, _ :: _, 0, h1, h2 => by simp_all [pmax]
  | _ :: l, _ :: m, a + 1, h1, h2 => by
    simp only [pmax, List.getD_cons_succ] at h1 h2 ⊢; exact getD_pmax_zero l m a h1 h2

theorem pmin_self : ∀ l : Part, pmin l l = l
  | [] => rfl
  | _ :: l => by simp [pmin, pmin_self l]

theorem pmax_self : ∀ l : Part, pmax l l = l
  | [] => rfl
  | _ :: l => by simp [pmax, pmax_self l]

theorem pmin_bump_left : ∀ a (l : Part), pmin (bump a l) l = l
  | a, [] => by cases a <;> rfl
  | 0, _ :: l => by simp [bump, pmin, pmin_self]
  | a + 1, _ :: l => by simp [bump, pmin, pmin_bump_left a l]

theorem pmin_bump_right : ∀ a (l : Part), pmin l (bump a l) = l
  | a, [] => by cases a <;> rfl
  | 0, _ :: l => by simp [bump, pmin, pmin_self]
  | a + 1, _ :: l => by simp [bump, pmin, pmin_bump_right a l]

theorem pmax_bump_left : ∀ a (l : Part), pmax (bump a l) l = bump a l
  | a, [] => by cases a <;> rfl
  | 0, _ :: l => by simp [bump, pmax, pmax_self]
  | a + 1, _ :: l => by simp [bump, pmax, pmax_bump_left a l]

theorem pmax_bump_right : ∀ a (l : Part), pmax l (bump a l) = bump a l
  | a, [] => by cases a <;> rfl
  | 0, _ :: l => by simp [bump, pmax, pmax_self]
  | a + 1, _ :: l => by simp [bump, pmax, pmax_bump_right a l]

theorem pmin_bump_bump : ∀ a b (l : Part), a ≠ b → pmin (bump a l) (bump b l) = l
  | a, b, [], _ => by cases a <;> cases b <;> rfl
  | 0, 0, _, h => absurd rfl h
  | 0, b + 1, _ :: l, _ => by simp [bump, pmin, pmin_bump_right]
  | a + 1, 0, _ :: l, _ => by simp [bump, pmin, pmin_bump_left]
  | a + 1, b + 1, _ :: l, h => by simp [bump, pmin, pmin_bump_bump a b l (by omega)]

theorem pmax_bump_bump : ∀ a b (l : Part), a ≠ b → pmax (bump a l) (bump b l) = bump b (bump a l)
  | a, b, [], _ => by cases a <;> cases b <;> rfl
  | 0, 0, _, h => absurd rfl h
  | 0, b + 1, _ :: l, _ => by simp [bump, pmax, pmax_bump_right]
  | a + 1, 0, _ :: l, _ => by simp [bump, pmax, pmax_bump_left]
  | a + 1, b + 1, _ :: l, h => by simp [bump, pmax, pmax_bump_bump a b l (by omega)]

/-! ## The local theorem -/

/-- `μ` is `ρ`, or `ρ` with one box added. -/
def Step (ρ μ : Part) : Prop := μ = ρ ∨ ∃ a, a < ρ.length ∧ μ = bump a ρ

/-- **The local theorem.** On every square that can occur, `bwd` undoes `fwd`. `hroom` says
a box that grew in the same row on both sides has a row below it to move into. -/
theorem bwd_fwd (ρ μ ν : Part) (x : Bool) (h0 : 0 < ρ.length)
    (hμ : Step ρ μ) (hν : Step ρ ν)
    (hroom : ∀ a, a < ρ.length → μ = bump a ρ → ν = bump a ρ → a + 1 < ρ.length)
    (hx : x = true → μ = ρ ∧ ν = ρ) :
    bwd μ ν (fwd ρ μ ν x) = (ρ, x) := by
  rcases hμ with hμ | ⟨a, ha, hμ⟩ <;> rcases hν with hν | ⟨b, hb, hν⟩ <;> subst μ <;> subst ν
  · -- nothing grew
    cases x with
    | false => simp [fwd, bwd]
    | true => simp [fwd, bwd, bump_ne h0, firstDiff_bump 0 _ h0]
  · -- only ν grew
    have hne : ρ ≠ bump b ρ := (bump_ne hb).symm
    have hxf : x = false := by
      cases x with
      | false => rfl
      | true => exact absurd (hx rfl).2.symm hne
    subst hxf
    simp [bwd, hne, pmin_bump_right]
  · -- only μ grew
    have hne : bump a ρ ≠ ρ := bump_ne ha
    have hxf : x = false := by
      cases x with
      | false => rfl
      | true => exact absurd (hx rfl).1 hne
    subst hxf
    simp [bwd, hne, pmin_bump_left]
  · -- both grew
    have hxf : x = false := by
      cases x with
      | false => rfl
      | true => exact absurd (hx rfl).1 (bump_ne ha)
    subst hxf
    by_cases hab : a = b
    · -- same row: the box is pushed one row lower
      subst hab
      have hl : a + 1 < (bump a ρ).length := by rw [length_bump]; exact hroom a ha rfl rfl
      simp [fwd, bwd, bump_ne ha, firstDiff_bump a ρ ha, bump_ne hl,
        firstDiff_bump (a + 1) _ hl, unbump_bump]
    · -- different rows: take the union
      simp [bwd, bump_ne_bump ha hb hab, pmin_bump_bump a b ρ hab]

/-- On such a square the top-right corner is again one box above each of `μ` and `ν`. -/
theorem fwd_step (ρ μ ν : Part) (x : Bool) (h0 : 0 < ρ.length)
    (hμ : Step ρ μ) (hν : Step ρ ν)
    (hroom : ∀ a, a < ρ.length → μ = bump a ρ → ν = bump a ρ → a + 1 < ρ.length)
    (hx : x = true → μ = ρ ∧ ν = ρ) :
    Step μ (fwd ρ μ ν x) ∧ Step ν (fwd ρ μ ν x) := by
  rcases hμ with hμ | ⟨a, ha, hμ⟩ <;> rcases hν with hν | ⟨b, hb, hν⟩ <;> subst μ <;> subst ν
  · cases x with
    | false => simp [fwd, Step]
    | true =>
      have e : fwd ρ ρ ρ true = bump 0 ρ := by simp [fwd]
      rw [e]; exact ⟨Or.inr ⟨0, h0, rfl⟩, Or.inr ⟨0, h0, rfl⟩⟩
  · have hne : ρ ≠ bump b ρ := (bump_ne hb).symm
    have hxf : x = false := by
      cases x with
      | false => rfl
      | true => exact absurd (hx rfl).2.symm hne
    subst hxf
    have e : fwd ρ ρ (bump b ρ) false = bump b ρ := by simp [fwd, hne, pmax_bump_right]
    rw [e]; exact ⟨Or.inr ⟨b, hb, rfl⟩, Or.inl rfl⟩
  · have hne : bump a ρ ≠ ρ := bump_ne ha
    have hxf : x = false := by
      cases x with
      | false => rfl
      | true => exact absurd (hx rfl).1 hne
    subst hxf
    have e : fwd ρ (bump a ρ) ρ false = bump a ρ := by simp [fwd, hne, pmax_bump_left]
    rw [e]; exact ⟨Or.inl rfl, Or.inr ⟨a, ha, rfl⟩⟩
  · have hxf : x = false := by
      cases x with
      | false => rfl
      | true => exact absurd (hx rfl).1 (bump_ne ha)
    subst hxf
    by_cases hab : a = b
    · subst hab
      have hl : a + 1 < (bump a ρ).length := by rw [length_bump]; exact hroom a ha rfl rfl
      have e : fwd ρ (bump a ρ) (bump a ρ) false = bump (a + 1) (bump a ρ) := by
        simp [fwd, bump_ne ha, firstDiff_bump a ρ ha]
      rw [e]; exact ⟨Or.inr ⟨a + 1, hl, rfl⟩, Or.inr ⟨a + 1, hl, rfl⟩⟩
    · have e : fwd ρ (bump a ρ) (bump b ρ) false = bump b (bump a ρ) := by
        simp [fwd, bump_ne_bump ha hb hab, pmax_bump_bump a b ρ hab]
      rw [e]
      refine ⟨Or.inr ⟨b, by rw [length_bump]; exact hb, rfl⟩,
        Or.inr ⟨a, by rw [length_bump]; exact ha, bump_comm _ _ _⟩⟩

theorem length_fwd {N} {ρ μ ν : Part} {x : Bool} (hρ : ρ.length = N) (hμ : μ.length = N)
    (hν : ν.length = N) : (fwd ρ μ ν x).length = N := by
  unfold fwd
  split
  · rw [length_pmax, hμ, hν, Nat.min_self]
  · split
    · split
      · rw [length_bump, hρ]
      · exact hρ
    · rw [length_bump, hμ]

/-! ## The grid, forwards and backwards -/

/-- The empty shape. -/
def zeros (N : Nat) : Part := List.replicate N 0

/-- The forward growth diagram, filled from the bottom-left corner. -/
def grow (σ : Nat → Nat → Bool) (N : Nat) : Nat → Nat → Part
  | 0, _ => zeros N
  | _, 0 => zeros N
  | i + 1, j + 1 => fwd (grow σ N i j) (grow σ N (i + 1) j) (grow σ N i (j + 1)) (σ i j)
termination_by i j => (i, j)

/-- The backward growth diagram, filled from the top-right corner using only the top edge
`top j = λ(n, j)` and the right edge `right i = λ(i, n)`. -/
def back (top right : Nat → Part) (n : Nat) (i j : Nat) : Part :=
  if n ≤ i then top j
  else if n ≤ j then right i
  else (bwd (back top right n (i + 1) j) (back top right n i (j + 1))
            (back top right n (i + 1) (j + 1))).1
termination_by (n - i, n - j)
decreasing_by all_goals (simp [Prod.lex_def]; omega)

/-- The matrix entry recovered at square `(i, j)` of the backward grid. -/
def backEntry (top right : Nat → Part) (n i j : Nat) : Bool :=
  (bwd (back top right n (i + 1) j) (back top right n i (j + 1))
       (back top right n (i + 1) (j + 1))).2

section Grid

variable (σ : Nat → Nat → Bool) (N : Nat)

theorem grow_zero_left (j : Nat) : grow σ N 0 j = zeros N := by simp [grow]

theorem grow_zero_right (i : Nat) : grow σ N i 0 = zeros N := by cases i <;> simp [grow]

theorem grow_succ (i j : Nat) : grow σ N (i + 1) (j + 1)
    = fwd (grow σ N i j) (grow σ N (i + 1) j) (grow σ N i (j + 1)) (σ i j) := by
  rw [grow]

theorem length_grow : ∀ i j, (grow σ N i j).length = N
  | 0, j => by simp [grow_zero_left, zeros]
  | i + 1, 0 => by simp [grow_zero_right, zeros]
  | i + 1, j + 1 => by
    rw [grow_succ]
    exact length_fwd (length_grow i j) (length_grow (i + 1) j) (length_grow i (j + 1))
termination_by i j => (i, j)

/-- The shape at `(i, j)` has no boxes in rows `≥ j`. -/
theorem supp_grow : ∀ i j a, j ≤ a → (grow σ N i j).getD a 0 = 0
  | 0, j, a, _ => by simp [grow_zero_left, zeros, List.getElem?_replicate]; split <;> rfl
  | i + 1, 0, a, _ => by simp [grow_zero_right, zeros, List.getElem?_replicate]; split <;> rfl
  | i + 1, j + 1, a, ha => by
    have hρ := supp_grow i j
    have hμ := supp_grow (i + 1) j
    have hν := supp_grow i (j + 1)
    rw [grow_succ]
    unfold fwd
    split
    · exact getD_pmax_zero _ _ a (hμ a (by omega)) (hν a ha)
    · split
      · split
        · rw [getD_bump_ne _ _ _ (by omega)]; exact hρ a (by omega)
        · exact hρ a (by omega)
      · rename_i hne
        have hspec := firstDiff_spec _ _ (by rw [length_grow, length_grow]) hne
        have hk : firstDiff (grow σ N (i + 1) j) (grow σ N i j) < j := by
          refine Nat.lt_of_not_le fun h => hspec.2 ?_
          rw [hμ _ h, hρ _ h]
        rw [getD_bump_ne _ _ _ (by omega)]; exact hμ a (by omega)
termination_by i j => (i, j)

/-- The invariants of square `(i, j)` of the forward grid: the hypotheses of `bwd_fwd`. -/
def SquareOK (i j : Nat) : Prop :=
  Step (grow σ N i j) (grow σ N (i + 1) j) ∧ Step (grow σ N i j) (grow σ N i (j + 1)) ∧
  (∀ a, a < (grow σ N i j).length → grow σ N (i + 1) j = bump a (grow σ N i j) →
    grow σ N i (j + 1) = bump a (grow σ N i j) → a + 1 < (grow σ N i j).length) ∧
  (σ i j = true → grow σ N (i + 1) j = grow σ N i j ∧ grow σ N i (j + 1) = grow σ N i j)

theorem SquareOK.step {σ N i j} (h : SquareOK σ N i j) (hN : 0 < N) :
    Step (grow σ N (i + 1) j) (grow σ N (i + 1) (j + 1)) ∧
    Step (grow σ N i (j + 1)) (grow σ N (i + 1) (j + 1)) := by
  rw [grow_succ]
  exact fwd_step _ _ _ _ (by rw [length_grow]; exact hN) h.1 h.2.1 h.2.2.1 h.2.2.2

/-- No `1` in row `i` left of column `j`: the shape does not grow from row `i` to `i+1`. -/
theorem row_flat (i : Nat) : ∀ j, (∀ j' < j, SquareOK σ N i j') → (∀ j' < j, σ i j' = false) →
    grow σ N (i + 1) j = grow σ N i j
  | 0, _, _ => by rw [grow_zero_right, grow_zero_right]
  | j + 1, hsq, hσ => by
    rw [grow_succ, row_flat i j (fun j' h => hsq j' (by omega)) (fun j' h => hσ j' (by omega)),
      hσ j (by omega)]
    rcases (hsq j (by omega)).2.1 with h | ⟨b, hb, h⟩
    · rw [h]; simp [fwd]
    · rw [h]; simp [fwd, (bump_ne hb).symm, pmax_bump_right]

/-- No `1` in column `j` below row `i`: the shape does not grow from column `j` to `j+1`. -/
theorem col_flat (j : Nat) : ∀ i, (∀ i' < i, SquareOK σ N i' j) → (∀ i' < i, σ i' j = false) →
    grow σ N i (j + 1) = grow σ N i j
  | 0, _, _ => by rw [grow_zero_left, grow_zero_left]
  | i + 1, hsq, hσ => by
    rw [grow_succ, col_flat j i (fun i' h => hsq i' (by omega)) (fun i' h => hσ i' (by omega)),
      hσ i (by omega)]
    rcases (hsq i (by omega)).1 with h | ⟨b, hb, h⟩
    · rw [h]; simp [fwd]
    · rw [h]; simp [fwd, bump_ne hb, pmax_bump_left]

/-- At most one `1` in each row and column. -/
def PartialPerm : Prop :=
  ∀ i j, σ i j = true → (∀ j', σ i j' = true → j' = j) ∧ (∀ i', σ i' j = true → i' = i)

/-- **Every square of the forward grid satisfies the hypotheses of the local theorem.**
One recursion over the grid, with the same lexicographic measure as `grow`. -/
theorem square_ok (n : Nat) (hσ : PartialPerm σ) : ∀ i j, j < n → SquareOK σ (n + 1) i j
  | i, j, hj => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- the shape grows by at most one box from row i to row i+1
      cases j with
      | zero => left; rw [grow_zero_right, grow_zero_right]
      | succ j' => exact (square_ok n hσ i j' (by omega)).step (by omega) |>.2
    · -- and from column j to column j+1
      cases i with
      | zero => left; rw [grow_zero_left, grow_zero_left]
      | succ i' => exact (square_ok n hσ i' j hj).step (by omega) |>.1
    · -- a box that grew on both sides has room to move down: it lies in a row < j < n
      intro a ha hμ _
      rw [length_grow] at ha ⊢
      have h1 := getD_bump_self a (grow σ (n + 1) i j) (by rw [length_grow]; exact ha)
      rw [← hμ] at h1
      have : a < j := Nat.lt_of_not_le fun h => by
        rw [supp_grow σ (n + 1) (i + 1) j a h] at h1; omega
      omega
    · -- a 1 sits where nothing grew, because its row and column hold no other 1
      intro hx
      obtain ⟨hrow, hcol⟩ := hσ i j hx
      constructor
      · refine row_flat σ (n + 1) i j (fun j' h => square_ok n hσ i j' (by omega)) ?_
        intro j' h
        cases e : σ i j' with
        | false => rfl
        | true => exact absurd (hrow j' e) (by omega)
      · refine col_flat σ (n + 1) j i (fun i' h => square_ok n hσ i' j hj) ?_
        intro i' h
        cases e : σ i' j with
        | false => rfl
        | true => exact absurd (hcol i' e) (by omega)
termination_by i j => (i, j)
decreasing_by all_goals (simp_wf; subst_vars; simp [Prod.lex_def]; try omega)

/-- **The backward grid rebuilds the forward grid** from its top and right edges. -/
theorem back_grow (n : Nat) (hσ : PartialPerm σ) : ∀ i j, i ≤ n → j ≤ n →
    back (fun j => grow σ (n + 1) n j) (fun i => grow σ (n + 1) i n) n i j = grow σ (n + 1) i j
  | i, j, hi, hj => by
    rw [back]
    split
    · have : i = n := by omega
      subst this; rfl
    · split
      · have : j = n := by omega
        subst this; rfl
      · rw [back_grow n hσ (i + 1) j (by omega) hj, back_grow n hσ i (j + 1) hi (by omega),
          back_grow n hσ (i + 1) (j + 1) (by omega) (by omega), grow_succ]
        obtain ⟨hμ, hν, hroom, hx⟩ := square_ok σ n hσ i j (by omega)
        rw [bwd_fwd _ _ _ _ (by rw [length_grow]; omega) hμ hν hroom hx]
termination_by i j => (n - i, n - j)

/-- **The backward grid recovers every matrix entry.** -/
theorem backEntry_grow (n : Nat) (hσ : PartialPerm σ) (i j : Nat) (hi : i < n) (hj : j < n) :
    backEntry (fun j => grow σ (n + 1) n j) (fun i => grow σ (n + 1) i n) n i j = σ i j := by
  unfold backEntry
  rw [back_grow σ n hσ (i + 1) j (by omega) (by omega), back_grow σ n hσ i (j + 1) (by omega)
    (by omega), back_grow σ n hσ (i + 1) (j + 1) (by omega) (by omega), grow_succ]
  obtain ⟨hμ, hν, hroom, hx⟩ := square_ok σ n hσ i j hj
  rw [bwd_fwd _ _ _ _ (by rw [length_grow]; omega) hμ hν hroom hx]

end Grid

/-! ## Permutations: P, Q and inverse RSK -/

/-- The permutation matrix of `π`: a `1` at `(i, π[i])`. -/
def perm (π : List Nat) : Nat → Nat → Bool := fun i j => π[i]? == some j

/-- Append `v` to row `k` of a tableau. -/
def addAt : Nat → Nat → List (List Nat) → List (List Nat)
  | 0, v, [] => [[v]]
  | 0, v, r :: rs => (r ++ [v]) :: rs
  | k + 1, v, [] => [] :: addAt k v []
  | k + 1, v, r :: rs => r :: addAt k v rs

/-- The tableau of a chain of shapes: label `k` goes in the box added at step `k`. -/
def chainTab (shape : Nat → Part) (n : Nat) : List (List Nat) :=
  (List.range n).foldl (fun t k => addAt (firstDiff (shape (k + 1)) (shape k)) k t) []

/-- RSK of a permutation by growth diagram: `(P, Q)`. -/
def rskGrowth (π : List Nat) : List (List Nat) × List (List Nat) :=
  let n := π.length
  let g := grow (perm π) (n + 1)
  (chainTab (fun j => g n j) n, chainTab (fun i => g i n) n)

/-- Inverse RSK by growth diagram: read the permutation back off the two outer edges. -/
def unrskGrowth (π : List Nat) : List Nat :=
  let n := π.length
  let g := grow (perm π) (n + 1)
  (List.range n).map fun i =>
    ((List.range n).find? fun j => backEntry (fun j => g n j) (fun i => g i n) n i j).getD 0

theorem perm_partialPerm (π : List Nat) (h : π.Nodup) : PartialPerm (perm π) := by
  intro i j hij
  simp only [perm, beq_iff_eq] at hij
  refine ⟨fun j' h' => ?_, fun i' h' => ?_⟩
  · simp only [perm, beq_iff_eq] at h'
    rw [hij] at h'; exact (Option.some.inj h').symm
  · simp only [perm, beq_iff_eq] at h'
    obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.mp hij
    obtain ⟨hi', e'⟩ := List.getElem?_eq_some_iff.mp h'
    exact (List.getElem_inj h).mp (e'.trans e.symm)

theorem find?_congr {α} (p q : α → Bool) : ∀ l : List α, (∀ x ∈ l, p x = q x) →
    l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.find?_cons, h x (by simp)]
    rw [find?_congr p q l (fun y hy => h y (by simp [hy]))]

theorem find?_range_eq (k : Nat) : ∀ n, k < n → (List.range n).find? (fun j => some k == some j)
    = some k
  | 0, h => absurd h (by omega)
  | n + 1, h => by
    rw [List.range_succ, List.find?_append]
    by_cases hk : k < n
    · rw [find?_range_eq k n hk]; rfl
    · have : k = n := by omega
      subst this
      have : (List.range k).find? (fun j => some k == some j) = none := by
        rw [List.find?_eq_none]; intro x hx; simp at hx ⊢; omega
      rw [this]; simp

/-- **Inverse RSK by growth diagram recovers every permutation** of `{0, …, n-1}`. -/
theorem unrskGrowth_rskGrowth (π : List Nat) (hnd : π.Nodup) (hlt : ∀ x ∈ π, x < π.length) :
    unrskGrowth π = π := by
  unfold unrskGrowth
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [find?_congr _ (fun j => perm π i j) _ (fun j hj => backEntry_grow (perm π) π.length
    (perm_partialPerm π hnd) i j (by simpa using h1) (by simpa using hj))]
  have hi : i < π.length := by simpa using h1
  simp only [perm, List.getElem?_eq_getElem hi]
  rw [find?_range_eq _ _ (hlt _ (List.getElem_mem _))]
  rfl

end RMT.RSK.Growth
