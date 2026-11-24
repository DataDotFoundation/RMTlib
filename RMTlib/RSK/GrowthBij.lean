import RMTlib.RSK.GrowthRoom

/-!
# The bosonic growth diagram is a bijection: ℕ-matrices and pairs of tableaux

Fill the `n × m` rectangle with a matrix `σ` of naturals and run the bosonic local rule
(`RMT.RSK.GrowthKnuth`, here as the all-bosonic case of `RMT.RSK.GrowthSuper`) with shapes of
`N ≥ m` rows. The top edge `j ↦ λ(n, j)` and the right edge `i ↦ λ(i, m)` are chains of
horizontal strips from the empty shape, that is, semistandard tableaux: `P` with entries `< m`
(the boxes of `λ(n, j+1) / λ(n, j)` hold `j`) and `Q` with entries `< n`. They end at the same
shape `λ(n, m)`. This file proves that every such pair arises from exactly one matrix, and that
the contents of `P` and `Q` are the column and row sums of `σ`. This is the RSK correspondence of
Knuth, in Fomin's growth-diagram form (Fomin 1995; Krattenthaler 2006, Theorem 2).

* `IsHChain N m c`: `c 0 = ∅` and `c (j+1) / c j` is a horizontal strip for `j < m`.

## Main results

* `isHChain_top`, `isHChain_right`: the two edges of every filling are chains of horizontal
  strips (no hypothesis on `N`).
* `backEntry_edges` (**left inverse**): for `m ≤ N`, the backward grid recovers the filling
  from its edges.
* `top_backEntry`, `right_backEntry` (**right inverse**): every pair of chains with the same
  last shape is the pair of edges of the filling read off by the backward grid.
* `size_top_succ`, `size_right_succ` (**weights**): `|λ(n, j+1)| − |λ(n, j)|` is the `j`-th
  column sum, and `|λ(i+1, m)| − |λ(i, m)|` the `i`-th row sum.

The local fact behind the right inverse is `fwdC_bwdC`: if `λ / μ` and `λ / ν` are horizontal
strips, the backward rule returns `ρ` and `x` with `μ / ρ`, `ν / ρ` horizontal strips and
`fwd ρ μ ν x = λ`. The boundary of the backward grid is empty because shapes only shrink
towards it and the two chains start empty.

Mathlib-free.
-/

namespace RMT.RSK.GrowthBij

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthGeneric (grow grow_zero_left grow_zero_right grow_succ back backEntry
  LocallyInvertible)
open RMT.RSK.GrowthSuper

/-- Every index is bosonic. -/
abbrev bos : Nat → Bool := fun _ => false

/-- The bosonic forward rule at every square. -/
abbrev Fb : Nat → Nat → Part → Part → Part → Nat → Part := GrowthSuper.F bos bos

/-- The bosonic backward rule at every square. -/
abbrev Bb : Nat → Nat → Part → Part → Part → Part × Nat := GrowthSuper.B bos bos

theorem admissible_bos (σ : Nat → Nat → Nat) : Admissible bos bos σ := fun _ _ => Or.inl rfl

/-- For two bosons the carry out of the last row is that of `RMT.RSK.GrowthKnuth`. -/
theorem carryOut_bosons : ∀ (t : Nat) (ρ μ ν : Part),
    GrowthSuper.carryOut false false t ρ μ ν = GrowthKnuth.carryOut t ρ μ ν
  | t, r :: ρ, a :: μ, b :: ν => by
    simp only [GrowthSuper.carryOut, GrowthKnuth.carryOut, carry]
    rw [carryOut_bosons]
    congr 1
    omega
  | _, [], _, _ => by simp [GrowthSuper.carryOut, GrowthKnuth.carryOut]
  | _, _ :: _, [], _ => by simp [GrowthSuper.carryOut, GrowthKnuth.carryOut]
  | _, _ :: _, _ :: _, [] => by simp [GrowthSuper.carryOut, GrowthKnuth.carryOut]

/-- The all-bosonic rule of `RMT.RSK.GrowthSuper` is the rule of `RMT.RSK.GrowthKnuth`. -/
theorem Fb_eq : Fb = GrowthKnuth.F := by
  funext i j ρ μ ν x
  exact fwdC_bosons x ρ μ ν

section Forward

variable (σ : Nat → Nat → Nat) (N n m : Nat)

/-- Bosonic room: shapes with `N ≥ m` rows never carry anything out of the last row. -/
theorem room_bos (hm : m ≤ N) : Room bos bos σ N n m := by
  intro i j _ hj
  have e : GrowthSuper.F bos bos = GrowthKnuth.F := Fb_eq
  rw [e]
  show GrowthSuper.carryOut false false _ _ _ _ = 0
  rw [carryOut_bosons]
  refine GrowthKnuth.carryOut_eq_zero _ _ _ _
    (by rw [GrowthKnuth.length_grow, GrowthKnuth.length_grow])
    (by rw [GrowthKnuth.length_grow, GrowthKnuth.length_grow])
    (by rw [GrowthKnuth.length_grow]; omega) ?_
  rw [GrowthKnuth.length_grow]
  exact GrowthKnuth.supp_grow σ _ (i + 1) j _ (by omega)

theorem locallyInvertible_bos (hm : m ≤ N) : LocallyInvertible Fb Bb (zeros N) σ n m :=
  locallyInvertible bos bos σ N (admissible_bos σ) n m (room_bos σ N n m hm)

/-- A chain of horizontal strips of length `m` from the empty shape with `N` rows: a
semistandard tableau with entries `< m`, the boxes of `c (j+1) / c j` holding `j`. -/
def IsHChain (N m : Nat) (c : Nat → Part) : Prop :=
  c 0 = zeros N ∧ ∀ j, j < m → HStrip (c j) (c (j + 1))

/-- The top edge of the growth diagram is a chain of horizontal strips. -/
theorem isHChain_top : IsHChain N m (fun j => grow Fb (zeros N) σ n j) :=
  ⟨grow_zero_right _ _ _ n, fun j _ => strip_grow_col bos bos σ N (admissible_bos σ) n j⟩

/-- The right edge of the growth diagram is a chain of horizontal strips. -/
theorem isHChain_right : IsHChain N n (fun i => grow Fb (zeros N) σ i m) :=
  ⟨grow_zero_left _ _ _ m, fun i _ => strip_grow_row bos bos σ N (admissible_bos σ) i m⟩

/-- **Left inverse.** For `m ≤ N`, the backward grid recovers every entry of the filling from
the two edges. -/
theorem backEntry_edges (hm : m ≤ N) (i j : Nat) (hi : i < n) (hj : j < m) :
    backEntry Bb (fun j => grow Fb (zeros N) σ n j) (fun i => grow Fb (zeros N) σ i m) n m i j
      = σ i j :=
  GrowthGeneric.backEntry_grow Fb Bb _ σ n m (locallyInvertible_bos σ N n m hm) i j hi hj

/-- **The weight of `P`.** The boxes of `λ(n, j+1) / λ(n, j)` number the `j`-th column sum. -/
theorem size_top_succ (hm : m ≤ N) (j : Nat) (hj : j < m) :
    size (grow Fb (zeros N) σ n (j + 1)) = size (grow Fb (zeros N) σ n j) + colSum σ j n := by
  rw [size_grow_of_room bos bos σ N (admissible_bos σ) n m (room_bos σ N n m hm) n (j + 1)
      (Nat.le_refl _) hj,
    size_grow_of_room bos bos σ N (admissible_bos σ) n m (room_bos σ N n m hm) n j
      (Nat.le_refl _) (by omega), rectSum_succ_right]

/-- **The weight of `Q`.** The boxes of `λ(i+1, m) / λ(i, m)` number the `i`-th row sum. -/
theorem size_right_succ (hm : m ≤ N) (i : Nat) (hi : i < n) :
    size (grow Fb (zeros N) σ (i + 1) m) = size (grow Fb (zeros N) σ i m) + rowSum σ i m := by
  rw [size_grow_of_room bos bos σ N (admissible_bos σ) n m (room_bos σ N n m hm) (i + 1) m hi
      (Nat.le_refl _),
    size_grow_of_room bos bos σ N (admissible_bos σ) n m (room_bos σ N n m hm) i m
      (by omega) (Nat.le_refl _)]
  rfl

end Forward

/-- The grid in the rectangle depends only on the entries in the rectangle. -/
theorem grow_congr {S E : Type} (F : Nat → Nat → S → S → S → E → S) (z : S)
    (σ τ : Nat → Nat → E) (n m : Nat) (h : ∀ i j, i < n → j < m → σ i j = τ i j) :
    ∀ i j, i ≤ n → j ≤ m → grow F z σ i j = grow F z τ i j
  | 0, j, _, _ => by rw [grow_zero_left, grow_zero_left]
  | i + 1, 0, _, _ => by rw [grow_zero_right, grow_zero_right]
  | i + 1, j + 1, hi, hj => by
    rw [grow_succ, grow_succ, grow_congr F z σ τ n m h i j (by omega) (by omega),
      grow_congr F z σ τ n m h (i + 1) j hi (by omega),
      grow_congr F z σ τ n m h i (j + 1) (by omega) hj, h i j (by omega) (by omega)]
termination_by i j => (i, j)

/-! ## The backward rule on horizontal strips -/

theorem bwdC_cons (p q : Bool) (a b l : Nat) (μ ν lam : Part) :
    bwdC p q (a :: μ) (b :: ν) (l :: lam)
      = ((min a b - carryB p q (bwdC p q μ ν lam).2 a b l) :: (bwdC p q μ ν lam).1,
        (bwdC p q μ ν lam).2 + l - max a b - carryB p q (bwdC p q μ ν lam).2 a b l) :=
  rfl

theorem HStrip.length_eq {a b : Part} (h : HStrip a b) : a.length = b.length :=
  Strip.length_eq (p := false) h

/-- **The backward rule on horizontal strips.** If `λ / μ` and `λ / ν` are horizontal strips, the
backward rule returns `ρ` and `x` such that the forward rule gives back `λ`, and `μ / ρ`, `ν / ρ`
are horizontal strips. The last conjunct (`x + max μ₀ ν₀ ≤ λ₀`) drives the induction. -/
theorem fwdC_bwdC : ∀ μ ν lam : Part, HStrip μ lam → HStrip ν lam →
    fwdC false false (bwdC false false μ ν lam).2 (bwdC false false μ ν lam).1 μ ν = lam ∧
    HStrip (bwdC false false μ ν lam).1 μ ∧ HStrip (bwdC false false μ ν lam).1 ν ∧
    (bwdC false false μ ν lam).2 + max (μ.headD 0) (ν.headD 0) ≤ lam.headD 0
  | [], [], [], _, _ => by simp [bwdC, fwdC, HStrip]
  | [a], [b], [l], hμ, hν => by
    simp only [HStrip] at hμ hν
    simp only [bwdC, carryB, fwdC, carry, HStrip, List.headD, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  | a :: a' :: μ, b :: b' :: ν, l :: l' :: lam, hμ, hν => by
    obtain ⟨hal, hla, hμ'⟩ := hμ
    obtain ⟨hbl, hlb, hν'⟩ := hν
    obtain ⟨ih1, ih2, ih3, ih4⟩ := fwdC_bwdC (a' :: μ) (b' :: ν) (l' :: lam) hμ' hν'
    have hlen := HStrip.length_eq ih2
    rw [bwdC_cons]
    generalize bwdC false false (a' :: μ) (b' :: ν) (l' :: lam) = p at ih1 ih2 ih3 ih4 hlen ⊢
    obtain ⟨ρ', s⟩ := p
    simp only [List.headD] at ih1 ih2 ih3 ih4 hlen ⊢
    match ρ', ih1, ih2, ih3, hlen with
    | r' :: ρ'', ih1, ih2, ih3, _ =>
      simp only [carryB]
      have e : s + l - max a b - s + min a b - (min a b - s) - (s + l - max a b - s) = s := by
        omega
      refine ⟨?_, ⟨by omega, by omega, ih2⟩, ⟨by omega, by omega, ih3⟩, by omega⟩
      rw [fwdC_cons]
      simp only [carry]
      rw [e, ih1, List.cons.injEq]
      exact ⟨by omega, rfl⟩
  | [], _, _ :: _, hμ, _ | _ :: _, _, [], hμ, _ | [_], _, _ :: _ :: _, hμ, _
  | _ :: _ :: _, _, [_], hμ, _ => by simp [HStrip] at hμ
  | [], _ :: _, [], _, hν | [_], [], [_], _, hν | [_], _ :: _ :: _, [_], _, hν
  | _ :: _ :: _, [], _ :: _ :: _, _, hν | _ :: _ :: _, [_], _ :: _ :: _, _, hν => by
    simp [HStrip] at hν

theorem allZero_of_relL : ∀ a b : Part, RelL false a b → (∀ x ∈ b, x = 0) → ∀ x ∈ a, x = 0
  | [], [], _, _ => by simp
  | x :: a, y :: b, ⟨hxy, h⟩, hb => by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · have := hb y (List.mem_cons_self ..)
      simp only [Rel] at hxy
      omega
    · exact allZero_of_relL a b h (fun w hw => hb w (List.mem_cons_of_mem _ hw)) z hz
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim

/-- A horizontal strip ending at the empty shape starts at the empty shape. -/
theorem eq_zeros_of_hstrip {N : Nat} {a : Part} (h : HStrip a (zeros N)) : a = zeros N := by
  have hl := HStrip.length_eq h
  have hz := allZero_of_relL a _ (Strip.relL (p := false) h)
    (fun x hx => by simp only [zeros] at hx; exact (List.mem_replicate.mp hx).2)
  simp only [zeros, List.length_replicate] at hl ⊢
  exact List.eq_replicate_iff.mpr ⟨hl, hz⟩

/-! ## The backward grid of a pair of chains -/

section Back

variable (N n m : Nat) (top right : Nat → Part)

theorem back_top (j : Nat) : back Bb top right n m n j = top j := by
  rw [back.eq_def]; simp

theorem back_right (hc : top m = right n) (i : Nat) (hi : i ≤ n) :
    back Bb top right n m i m = right i := by
  rw [back.eq_def]
  split
  · have : i = n := by omega
    subst this
    exact hc
  · simp

theorem back_inner (i j : Nat) (hi : i < n) (hj : j < m) :
    back Bb top right n m i j = (Bb i j (back Bb top right n m (i + 1) j)
      (back Bb top right n m i (j + 1)) (back Bb top right n m (i + 1) (j + 1))).1 := by
  rw [back.eq_def]
  simp [Nat.not_le.mpr hi, Nat.not_le.mpr hj]

variable {N n m top right}

/-- In the backward grid of two chains of horizontal strips with the same last shape, every
edge is a horizontal strip. -/
theorem strip_back (htop : IsHChain N m top) (hright : IsHChain N n right)
    (hc : top m = right n) : ∀ i j, i ≤ n → j ≤ m →
      (j < m → HStrip (back Bb top right n m i j) (back Bb top right n m i (j + 1))) ∧
      (i < n → HStrip (back Bb top right n m i j) (back Bb top right n m (i + 1) j))
  | i, j, hi, hj => by
    by_cases hin : i = n
    · subst hin
      refine ⟨fun hjm => ?_, fun h => absurd h (Nat.lt_irrefl _)⟩
      rw [back_top, back_top]
      exact htop.2 j hjm
    by_cases hjm : j = m
    · subst hjm
      refine ⟨fun h => absurd h (Nat.lt_irrefl _), fun hin' => ?_⟩
      rw [back_right _ _ top right hc i hi, back_right _ _ top right hc (i + 1) hin']
      exact hright.2 i hin'
    have h1 := strip_back htop hright hc (i + 1) j (by omega) hj
    have h2 := strip_back htop hright hc i (j + 1) hi (by omega)
    obtain ⟨-, h3, h4, -⟩ := fwdC_bwdC _ _ _ (h1.1 (by omega)) (h2.2 (by omega))
    rw [back_inner _ _ top right i j (by omega) (by omega)]
    exact ⟨fun _ => h4, fun _ => h3⟩
termination_by i j => (n - i) + (m - j)

theorem back_zero_left (htop : IsHChain N m top) (hright : IsHChain N n right)
    (hc : top m = right n) : ∀ j, j ≤ m → back Bb top right n m 0 j = zeros N
  | j, hj => by
    by_cases hjm : j = m
    · subst hjm
      rw [back_right _ _ top right hc 0 (Nat.zero_le _)]
      exact hright.1
    have ih := back_zero_left htop hright hc (j + 1) (by omega)
    have h := (strip_back htop hright hc 0 j (Nat.zero_le _) hj).1 (by omega)
    rw [ih] at h
    exact eq_zeros_of_hstrip h
termination_by j => m - j

theorem back_zero_bottom (htop : IsHChain N m top) (hright : IsHChain N n right)
    (hc : top m = right n) : ∀ i, i ≤ n → back Bb top right n m i 0 = zeros N
  | i, hi => by
    by_cases hin : i = n
    · subst hin
      rw [back_top]
      exact htop.1
    have ih := back_zero_bottom htop hright hc (i + 1) (by omega)
    have h := (strip_back htop hright hc i 0 hi (Nat.zero_le _)).2 (by omega)
    rw [ih] at h
    exact eq_zeros_of_hstrip h
termination_by i => n - i

/-- The forward grid of the entries read off by the backward grid is the backward grid. -/
theorem grow_backEntry (htop : IsHChain N m top) (hright : IsHChain N n right)
    (hc : top m = right n) : ∀ i j, i ≤ n → j ≤ m →
      grow Fb (zeros N) (backEntry Bb top right n m) i j = back Bb top right n m i j
  | 0, j, _, hj => by rw [grow_zero_left, back_zero_left htop hright hc j hj]
  | i + 1, 0, hi, _ => by rw [grow_zero_right, back_zero_bottom htop hright hc (i + 1) hi]
  | i + 1, j + 1, hi, hj => by
    rw [grow_succ, grow_backEntry htop hright hc i j (by omega) (by omega),
      grow_backEntry htop hright hc (i + 1) j hi (by omega),
      grow_backEntry htop hright hc i (j + 1) (by omega) hj]
    have h1 := strip_back htop hright hc (i + 1) j hi (by omega)
    have h2 := strip_back htop hright hc i (j + 1) (by omega) hj
    obtain ⟨h, -, -, -⟩ := fwdC_bwdC _ _ _ (h1.1 (by omega)) (h2.2 (by omega))
    rw [back_inner _ _ top right i j (by omega) (by omega)]
    exact h
termination_by i j => (i, j)

/-- **Right inverse, top edge.** -/
theorem top_backEntry (htop : IsHChain N m top) (hright : IsHChain N n right)
    (hc : top m = right n) (j : Nat) (hj : j ≤ m) :
    grow Fb (zeros N) (backEntry Bb top right n m) n j = top j := by
  rw [grow_backEntry htop hright hc n j (Nat.le_refl _) hj, back_top]

/-- **Right inverse, right edge.** -/
theorem right_backEntry (htop : IsHChain N m top) (hright : IsHChain N n right)
    (hc : top m = right n) (i : Nat) (hi : i ≤ n) :
    grow Fb (zeros N) (backEntry Bb top right n m) i m = right i := by
  rw [grow_backEntry htop hright hc i m hi (Nat.le_refl _), back_right _ _ top right hc i hi]

end Back

end RMT.RSK.GrowthBij
