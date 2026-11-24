import RMTlib.RSK.GrowthStrips

/-!
# Room from a size bound

`RMT.RSK.GrowthSuper.locallyInvertible` needs *room*: no square of the growth diagram carries
anything out of the last row of its shapes (`Room`). This file proves that room holds as soon as
the shapes have at least as many rows as the total of the filling.

The argument has two parts.

* **Conservation** (`size_fwdC`): on every square, `|λ| + carryOut + |ρ| = |μ| + |ν| + x`.
  Boxes are neither created nor lost; whatever is not placed in `λ` leaves through the bottom.
* **A carry out of the last row fills every row** (`one_le_of_carryOut_ne_zero`): if something is
  carried out of the last row and `λ` is a partition, then every row of `λ` is non-empty, so
  `|λ| ≥ N`.

By induction over the grid, `|λ(i, j)|` is then the sum of the entries of the filling below and
to the left of `(i, j)` (`size_grow`), and a carry out of the last row would force that sum to
exceed `N`.

## Main results

* `room_of_rectSum_le`: for an admissible parity-labelled filling whose entries in the `n × m`
  rectangle sum to at most `N`, `Room` holds with shapes of length `N`.
* `locallyInvertible_of_rectSum_le`, `eq_of_edges_of_rectSum_le`: local invertibility and
  injectivity with the size bound in place of `Room`.
* `size_grow`: under the same bound, `|λ(i, j)| = Σ_{i' < i, j' < j} σ i' j'`.

The bound is the one the exhaustive checks of `scripts/growth_rules.py` report
(`|μ| + |ν| − |ρ| + x ≤ N` on each square). It is sharp for two fermions, where a single entry
`x` in an empty square needs `x` rows.

Mathlib-free.
-/

namespace RMT.RSK.GrowthSuper

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthGeneric (grow grow_zero_left grow_zero_right grow_succ LocallyInvertible)

/-- The size (number of boxes) of a padded shape. -/
def size (l : Part) : Nat := l.sum

@[simp] theorem size_nil : size [] = 0 := rfl

@[simp] theorem size_cons (a : Nat) (l : Part) : size (a :: l) = a + size l := by
  simp [size, List.sum_cons]

theorem size_zeros : ∀ N, size (zeros N) = 0
  | 0 => rfl
  | N + 1 => by
    have := size_zeros N
    simp only [zeros, List.replicate_succ, size_cons] at this ⊢
    omega

theorem Rel.le {p : Bool} {r a : Nat} (h : Rel p r a) : r ≤ a := by
  cases p
  · exact h
  · exact h.1

/-! ## One square -/

/-- **Conservation of boxes** on one square: `|λ| + carryOut + |ρ| = |μ| + |ν| + t`. -/
theorem size_fwdC (p q : Bool) : ∀ (t : Nat) (ρ μ ν : Part), RelL p ρ μ → RelL q ρ ν →
    CarryOK p q t → size (fwdC p q t ρ μ ν) + carryOut p q t ρ μ ν + size ρ
      = size μ + size ν + t
  | t, [], [], [], _, _, _ => by simp [fwdC, carryOut]
  | t, r :: ρ, a :: μ, b :: ν, ⟨ha, hμ⟩, ⟨hb, hν⟩, ht => by
    obtain ⟨-, -, h3, -, -, h6⟩ := digit p q r a b t ha hb ht
    have ih := size_fwdC p q _ ρ μ ν hμ hν h3
    have hra := ha.le
    have hrb := hb.le
    simp only [fwdC, carryOut, size_cons] at ih h6 ⊢
    omega

/-- In one row: if a carry leaves the row, the row of `λ` is non-empty. -/
theorem one_le_of_carry_ne_zero (p q : Bool) (r a b t : Nat) (ha : Rel p r a)
    (hb : Rel q r b) (h : t + min a b - r - carry p q t r a b ≠ 0) :
    1 ≤ max a b + carry p q t r a b := by
  have hra := ha.le
  have hrb := hb.le
  cases p <;> cases q <;> simp only [carry] at h ⊢ <;> omega

/-- **A carry out of the last row fills every row**: if `λ = fwdC p q t ρ μ ν` is a partition and
something is carried out of its last row, every row of `λ` holds at least one box. -/
theorem one_le_of_carryOut_ne_zero (p q : Bool) : ∀ (t : Nat) (ρ μ ν : Part), RelL p ρ μ →
    RelL q ρ ν → CarryOK p q t → carryOut p q t ρ μ ν ≠ 0 → Partition (fwdC p q t ρ μ ν) →
    ∀ x ∈ fwdC p q t ρ μ ν, 1 ≤ x
  | t, [], [], [], _, _, _, _, _ => by simp [fwdC]
  | t, [r], [a], [b], ⟨ha, _⟩, ⟨hb, _⟩, _, h, _ => by
    simp only [carryOut] at h
    simp only [fwdC, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact one_le_of_carry_ne_zero p q r a b t ha hb h
  | t, r :: r' :: ρ, a :: a' :: μ, b :: b' :: ν, ⟨ha, hμ⟩, ⟨hb, hν⟩, ht, h, hp => by
    obtain ⟨-, -, h3, -, -, -⟩ := digit p q r a b t ha hb ht
    simp only [carryOut] at h
    rw [fwdC_cons] at hp ⊢
    have ih := one_le_of_carryOut_ne_zero p q _ (r' :: ρ) (a' :: μ) (b' :: ν) hμ hν h3 h
      (by exact (match hp with | ⟨_, h⟩ => h : Partition _))
    rw [fwdC_cons] at hp ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have h1 := ih _ (List.mem_cons_self ..)
      exact Nat.le_trans h1 hp.1
    · exact ih x hx
  | _, [], _ :: _, _, h, _, _, _, _ | _, _ :: _, [], _, h, _, _, _, _
  | _, [_], _ :: _ :: _, _, h, _, _, _, _ | _, _ :: _ :: _, [_], _, h, _, _, _, _ => by
    simp [RelL] at h
  | _, [], [], _ :: _, _, h, _, _, _ | _, [_], [_], [], _, h, _, _, _
  | _, [_], [_], _ :: _ :: _, _, h, _, _, _ | _, _ :: _ :: _, _ :: _ :: _, [], _, h, _, _, _
  | _, _ :: _ :: _, _ :: _ :: _, [_], _, h, _, _, _ => by
    simp [RelL] at h

theorem length_le_size_of_one_le : ∀ l : Part, (∀ x ∈ l, 1 ≤ x) → l.length ≤ size l
  | [], _ => Nat.le_refl _
  | a :: l, h => by
    have := length_le_size_of_one_le l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h a (List.mem_cons_self ..)
    simp only [List.length_cons, size_cons]
    omega

/-! ## Sums over rectangles -/

/-- `Σ_{j' < j} σ i j'`. -/
def rowSum (σ : Nat → Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => rowSum σ i j + σ i j

/-- `Σ_{i' < i, j' < j} σ i' j'`: the sum of the entries in the `i × j` rectangle. -/
def rectSum (σ : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | i + 1, j => rectSum σ i j + rowSum σ i j

theorem rowSum_mono (σ : Nat → Nat → Nat) (i : Nat) {j j' : Nat} (h : j ≤ j') :
    rowSum σ i j ≤ rowSum σ i j' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => simp only [rowSum]; omega

theorem rectSum_mono (σ : Nat → Nat → Nat) {i i' j j' : Nat} (hi : i ≤ i') (hj : j ≤ j') :
    rectSum σ i j ≤ rectSum σ i' j' := by
  have h1 : rectSum σ i j ≤ rectSum σ i j' := by
    induction i with
    | zero => exact Nat.le_refl _
    | succ i ih =>
      simp only [rectSum]
      have := rowSum_mono σ i hj
      have := ih (by omega)
      omega
  refine Nat.le_trans h1 ?_
  induction hi with
  | refl => exact Nat.le_refl _
  | step _ ih => simp only [rectSum]; omega

/-- The rectangle sums satisfy the local rule of sizes. -/
theorem rectSum_succ_succ (σ : Nat → Nat → Nat) (i j : Nat) :
    rectSum σ (i + 1) (j + 1) + rectSum σ i j
      = rectSum σ (i + 1) j + rectSum σ i (j + 1) + σ i j := by
  simp only [rectSum, rowSum]; omega

/-- `Σ_{i' < i} σ i' j`. -/
def colSum (σ : Nat → Nat → Nat) (j : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => colSum σ j i + σ i j

/-- Adding a column to the rectangle adds a column sum. -/
theorem rectSum_succ_right (σ : Nat → Nat → Nat) (j : Nat) :
    ∀ i, rectSum σ i (j + 1) = rectSum σ i j + colSum σ j i
  | 0 => rfl
  | i + 1 => by
    have := rectSum_succ_right σ j i
    simp only [rectSum, rowSum, colSum] at this ⊢
    omega

@[simp] theorem rectSum_zero_right (σ : Nat → Nat → Nat) : ∀ i, rectSum σ i 0 = 0
  | 0 => rfl
  | i + 1 => by simp [rectSum, rowSum, rectSum_zero_right σ i]

/-! ## The grid -/

section Grid

variable (rp cp : Nat → Bool) (σ : Nat → Nat → Nat) (N : Nat)

/-- Under the size bound, the shapes of the growth diagram in the rectangle have size the
rectangle sum, and no square carries anything out of its last row. -/
theorem size_grow_and_room (hσ : Admissible rp cp σ) (n m : Nat) (hN : rectSum σ n m ≤ N) :
    ∀ i j, i ≤ n → j ≤ m →
      size (grow (F rp cp) (zeros N) σ i j) = rectSum σ i j ∧
      (0 < i → 0 < j → carryOut (rp (i - 1)) (cp (j - 1)) (σ (i - 1) (j - 1))
        (grow (F rp cp) (zeros N) σ (i - 1) (j - 1)) (grow (F rp cp) (zeros N) σ i (j - 1))
        (grow (F rp cp) (zeros N) σ (i - 1) j) = 0)
  | 0, j, _, _ => by
    refine ⟨?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
    rw [grow_zero_left, size_zeros]; rfl
  | i + 1, 0, _, _ => by
    refine ⟨?_, fun _ h => absurd h (Nat.lt_irrefl 0)⟩
    rw [grow_zero_right, size_zeros, rectSum_zero_right]
  | i + 1, j + 1, hi, hj => by
    have hs := strip_grow rp cp σ N hσ i j
    have hρ := (size_grow_and_room hσ n m hN i j (by omega) (by omega)).1
    have hμ := (size_grow_and_room hσ n m hN (i + 1) j hi (by omega)).1
    have hν := (size_grow_and_room hσ n m hN i (j + 1) (by omega) hj).1
    have hcons := size_fwdC (rp i) (cp j) (σ i j) _ _ _ hs.2.1.relL hs.2.2.relL (hσ i j)
    rw [hρ, hμ, hν] at hcons
    have hsum := rectSum_succ_succ σ i j
    have hbound := rectSum_mono σ hi hj
    have hco : carryOut (rp i) (cp j) (σ i j) (grow (F rp cp) (zeros N) σ i j)
        (grow (F rp cp) (zeros N) σ (i + 1) j) (grow (F rp cp) (zeros N) σ i (j + 1)) = 0 := by
      apply Classical.byContradiction
      intro hne
      have hall := one_le_of_carryOut_ne_zero (rp i) (cp j) (σ i j) _ _ _ hs.2.1.relL
        hs.2.2.relL (hσ i j) hne (partition_fwdC _ _ _ _ _ _ hs.1 hs.2.1 hs.2.2 (hσ i j))
      have hlen := length_le_size_of_one_le _ hall
      have hlen' := length_grow rp cp σ N (i + 1) (j + 1)
      rw [grow_succ] at hlen'
      simp only [F] at hlen'
      rw [hlen'] at hlen
      have : 0 < carryOut (rp i) (cp j) (σ i j) (grow (F rp cp) (zeros N) σ i j)
        (grow (F rp cp) (zeros N) σ (i + 1) j) (grow (F rp cp) (zeros N) σ i (j + 1)) :=
        Nat.pos_of_ne_zero hne
      omega
    refine ⟨?_, fun _ _ => hco⟩
    rw [grow_succ]
    simp only [F]
    omega
termination_by i j => (i, j)

/-- With room, `|λ(i, j)|` is the sum of the entries below and to the left of `(i, j)`. -/
theorem size_grow_of_room (hσ : Admissible rp cp σ) (n m : Nat) (hroom : Room rp cp σ N n m) :
    ∀ i j, i ≤ n → j ≤ m → size (grow (F rp cp) (zeros N) σ i j) = rectSum σ i j
  | 0, j, _, _ => by rw [grow_zero_left, size_zeros]; rfl
  | i + 1, 0, _, _ => by rw [grow_zero_right, size_zeros, rectSum_zero_right]
  | i + 1, j + 1, hi, hj => by
    have hs := strip_grow rp cp σ N hσ i j
    have hρ := size_grow_of_room hσ n m hroom i j (by omega) (by omega)
    have hμ := size_grow_of_room hσ n m hroom (i + 1) j hi (by omega)
    have hν := size_grow_of_room hσ n m hroom i (j + 1) (by omega) hj
    have hcons := size_fwdC (rp i) (cp j) (σ i j) _ _ _ hs.2.1.relL hs.2.2.relL (hσ i j)
    rw [hρ, hμ, hν, hroom i j (by omega) (by omega)] at hcons
    have hsum := rectSum_succ_succ σ i j
    rw [grow_succ]
    simp only [F]
    omega
termination_by i j => (i, j)

/-- **Room from a size bound.** If the entries of an admissible parity-labelled filling in the
`n × m` rectangle sum to at most `N`, no square of the rectangle carries anything out of the last
row of shapes of length `N`. -/
theorem room_of_rectSum_le (hσ : Admissible rp cp σ) (n m : Nat) (hN : rectSum σ n m ≤ N) :
    Room rp cp σ N n m := by
  intro i j hi hj
  exact (size_grow_and_room rp cp σ N hσ n m hN (i + 1) (j + 1) hi hj).2 (Nat.succ_pos _)
    (Nat.succ_pos _)

/-- Under the size bound, `|λ(i, j)|` is the sum of the entries below and to the left of
`(i, j)`. -/
theorem size_grow (hσ : Admissible rp cp σ) (n m : Nat) (hN : rectSum σ n m ≤ N) (i j : Nat)
    (hi : i ≤ n) (hj : j ≤ m) : size (grow (F rp cp) (zeros N) σ i j) = rectSum σ i j :=
  (size_grow_and_room rp cp σ N hσ n m hN i j hi hj).1

/-- **Local invertibility from a size bound.** -/
theorem locallyInvertible_of_rectSum_le (hσ : Admissible rp cp σ) (n m : Nat)
    (hN : rectSum σ n m ≤ N) : LocallyInvertible (F rp cp) (B rp cp) (zeros N) σ n m :=
  locallyInvertible rp cp σ N hσ n m (room_of_rectSum_le rp cp σ N hσ n m hN)

/-- **Injectivity from a size bound.** Two admissible parity-labelled fillings whose entries in
the `n × m` rectangle sum to at most `N`, and whose growth diagrams have the same top and right
edges, agree on the rectangle. -/
theorem eq_of_edges_of_rectSum_le (τ : Nat → Nat → Nat) (hσ : Admissible rp cp σ)
    (hτ : Admissible rp cp τ) (n m : Nat) (hNσ : rectSum σ n m ≤ N) (hNτ : rectSum τ n m ≤ N)
    (htop : ∀ j, j ≤ m → grow (F rp cp) (zeros N) σ n j = grow (F rp cp) (zeros N) τ n j)
    (hright : ∀ i, i ≤ n → grow (F rp cp) (zeros N) σ i m = grow (F rp cp) (zeros N) τ i m) :
    ∀ i j, i < n → j < m → σ i j = τ i j :=
  eq_of_edges rp cp σ N τ hσ hτ n m (room_of_rectSum_le rp cp σ N hσ n m hNσ)
    (room_of_rectSum_le rp cp τ N hτ n m hNτ) htop hright

end Grid

end RMT.RSK.GrowthSuper
