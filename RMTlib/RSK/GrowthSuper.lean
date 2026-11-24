import RMTlib.RSK.GrowthKnuth

/-!
# Growth diagrams labelled by parity: one local rule for bosons and fermions

Each row `i` and each column `j` of a filling carries a parity, `false` for a boson and `true`
for a fermion. Along a bosonic index the shapes grow by horizontal strips, along a fermionic
index by vertical strips. Cells of like parity hold entries in `ℕ`, mixed cells hold `0` or `1`.
This is the setting of super-RSK and of the super Cauchy identity
`∏_{like} (1 − x y)⁻¹ ∏_{mixed} (1 + x y) = Σ_λ hs_λ(x) hs_λ(y)`.

All four parity types use ONE local rule, a carry running down the rows with a cap that depends
on the type. With `ρ, μ, ν` the shapes at the bottom-left, bottom-right and top-left of a
square, `t₀ = x` the entry, and row by row

    c_k = min t_k cap_k,    λ_k = max μ_k ν_k + c_k,    t_{k+1} = t_k + min μ_k ν_k − ρ_k − c_k,

where `cap_k` is `∞` for two bosons (this is `RMT.RSK.GrowthKnuth`), `[ν_k ≤ μ_k]` for a bosonic
row and fermionic column, `[μ_k ≤ ν_k]` for the converse, and `[μ_k = ν_k = ρ_k]` for two
fermions. The backward rule is the same machine run from the bottom row up. On all four types the
rules encode N. Hage's super-RSK (arXiv:2206.15451); the rule for two fermions is also the one
forced by Muth's super-RSK (arXiv:1711.00420). It is not the conjugate of the bosonic rule, which
is Bonetti–Senato–Venezia's. Berele–Regev's own insertion handles words only, so it never meets a
square of two fermions (see `scripts/README.md`).
The rules were found and checked exhaustively in Python before being proved here.

The point of this formulation for Lean is that invertibility is *per digit*: it needs only, in
each row `k`, the relation of `ρ_k` to `μ_k` and to `ν_k` (`ρ_k ≤ μ_k`, and `μ_k ≤ ρ_k + 1` on a
fermionic side), a bound `t ≤ 1` on the carry in mixed cells, and no carry out of the last row.
Each row is then a finite arithmetic check (`digit`), and the rest is one list induction.

## Main results

* `digit`: the per-row identity, for all four parity types.
* `bwd_fwd`: the backward rule undoes the forward rule on every square satisfying the per-row
  relations, the carry bound and room in the last row.
* `rel_fwd_left`, `rel_fwd_right`: the result again relates to `μ` and `ν` in the right way.
* `locallyInvertible`, `eq_of_edges`: for parity-labelled fillings with no carry out of the last
  row at any square, the growth diagram is locally invertible, so the filling is determined by
  the outer edges.

That enough rows always give room is proved in `RMTlib.RSK.GrowthRoom`
(`room_of_rectSum_le`: shapes of length at least the total of the filling suffice). Not yet
proved: the identification of the edges with super tableaux.

Mathlib-free.
-/

namespace RMT.RSK.GrowthSuper

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthGeneric (grow grow_zero_left grow_zero_right grow_succ LocallyInvertible)

/-- The carry deposited in a row: `t` capped according to the parity type `(p, q)` of the
square (`p` the row parity, `q` the column parity). -/
def carry : Bool → Bool → Nat → Nat → Nat → Nat → Nat
  | false, false, t, _, _, _ => t
  | false, true, t, _, a, b => min t (a + 1 - max a b)
  | true, false, t, _, a, b => min t (b + 1 - max a b)
  | true, true, t, r, a, b => min t (r + 1 - max a b)

/-- The carry taken back from a row by the backward rule, from `μ_k`, `ν_k`, `λ_k`. -/
def carryB : Bool → Bool → Nat → Nat → Nat → Nat → Nat
  | false, false, s, _, _, _ => s
  | false, true, s, a, b, _ => min s (min a b + 1 - b)
  | true, false, s, a, b, _ => min s (min a b + 1 - a)
  | true, true, s, a, b, l => min s (min a b + 1 - l)

/-- How a shape grows along an index of parity `p`, in one row: by at most one box for a
fermion (vertical strip), by any number for a boson (horizontal strip). -/
def Rel : Bool → Nat → Nat → Prop
  | false, r, a => r ≤ a
  | true, r, a => r ≤ a ∧ a ≤ r + 1

/-- The bound on carries: none for like parities, at most one for mixed ones. -/
def CarryOK (p q : Bool) (t : Nat) : Prop := p = q ∨ t ≤ 1

/-- **The per-row identity.** In one row, under the relations of `ρ_k` to `μ_k` and `ν_k` and the
carry bound, the backward rule recovers `ρ_k` and the incoming carry from the outgoing one; the
outgoing carry satisfies the bound again; and `λ_k` relates to `ν_k` and `μ_k` in the right way. -/
theorem digit (p q : Bool) (r a b t : Nat) (ha : Rel p r a) (hb : Rel q r b)
    (ht : CarryOK p q t) :
    let c := carry p q t r a b
    let l := max a b + c
    let t' := t + min a b - r - c
    min a b - carryB p q t' a b l = r ∧ t' + l - max a b - carryB p q t' a b l = t ∧
      CarryOK p q t' ∧ Rel p b l ∧ Rel q a l ∧ r + c ≤ t + min a b := by
  intro c l t'
  have hc : c = carry p q t r a b := rfl
  have hl : l = max a b + c := rfl
  have ht' : t' = t + min a b - r - c := rfl
  generalize c = c0 at *
  generalize l = l0 at *
  generalize t' = t0 at *
  cases p <;> cases q <;>
    simp only [carry, carryB, Rel, CarryOK, Nat.min_def, Nat.max_def, Bool.false_eq_true,
      Bool.true_eq_false, false_or, true_or] at ha hb ht hc hl ht' ⊢ <;>
    and_intros <;>
    repeat' (first | split at hc | split at hl | split at ht' | split)
  all_goals first | trivial | omega

/-! ## One square -/

/-- The forward rule with incoming carry `t`. -/
def fwdC (p q : Bool) : Nat → Part → Part → Part → Part
  | t, r :: ρ, a :: μ, b :: ν =>
    (max a b + carry p q t r a b) :: fwdC p q (t + min a b - r - carry p q t r a b) ρ μ ν
  | _, _, _, _ => []

/-- The carry out of the last row. -/
def carryOut (p q : Bool) : Nat → Part → Part → Part → Nat
  | t, r :: ρ, a :: μ, b :: ν => carryOut p q (t + min a b - r - carry p q t r a b) ρ μ ν
  | t, _, _, _ => t

/-- The backward rule: the shape `ρ` and the carry into the first row (the entry). -/
def bwdC (p q : Bool) : Part → Part → Part → Part × Nat
  | a :: μ, b :: ν, l :: lam =>
    let s := (bwdC p q μ ν lam).2
    ((min a b - carryB p q s a b l) :: (bwdC p q μ ν lam).1,
      s + l - max a b - carryB p q s a b l)
  | _, _, _ => ([], 0)

/-- The relation `Rel p` in every row. -/
def RelL (p : Bool) : Part → Part → Prop
  | [], [] => True
  | r :: ρ, a :: μ => Rel p r a ∧ RelL p ρ μ
  | _, _ => False

theorem RelL.length_eq {p : Bool} : ∀ {l m : Part}, RelL p l m → l.length = m.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [RelL.length_eq h.2]

theorem RelL.refl (p : Bool) : ∀ l : Part, RelL p l l
  | [] => trivial
  | _ :: l => ⟨by cases p <;> simp [Rel], RelL.refl p l⟩

/-- **The local theorem**, for all four parity types. -/
theorem bwd_fwd (p q : Bool) : ∀ (t : Nat) (ρ μ ν : Part), RelL p ρ μ → RelL q ρ ν →
    CarryOK p q t → carryOut p q t ρ μ ν = 0 → bwdC p q μ ν (fwdC p q t ρ μ ν) = (ρ, t)
  | t, [], [], [], _, _, _, h => by simp [carryOut] at h; simp [bwdC, h]
  | t, r :: ρ, a :: μ, b :: ν, ⟨ha, hμ⟩, ⟨hb, hν⟩, ht, h => by
    obtain ⟨h1, h2, h3, -, -, -⟩ := digit p q r a b t ha hb ht
    simp only [carryOut] at h
    simp only [fwdC, bwdC, bwd_fwd p q _ ρ μ ν hμ hν h3 h]
    rw [h1, h2]

/-- The result relates to `ν` along the row index (parity `p`). -/
theorem rel_fwd_right (p q : Bool) : ∀ (t : Nat) (ρ μ ν : Part), RelL p ρ μ → RelL q ρ ν →
    CarryOK p q t → RelL p ν (fwdC p q t ρ μ ν)
  | _, [], [], [], _, _, _ => trivial
  | t, r :: ρ, a :: μ, b :: ν, ⟨ha, hμ⟩, ⟨hb, hν⟩, ht => by
    obtain ⟨-, -, h3, h4, -, -⟩ := digit p q r a b t ha hb ht
    exact ⟨h4, rel_fwd_right p q _ ρ μ ν hμ hν h3⟩

/-- The result relates to `μ` along the column index (parity `q`). -/
theorem rel_fwd_left (p q : Bool) : ∀ (t : Nat) (ρ μ ν : Part), RelL p ρ μ → RelL q ρ ν →
    CarryOK p q t → RelL q μ (fwdC p q t ρ μ ν)
  | _, [], [], [], _, _, _ => trivial
  | t, r :: ρ, a :: μ, b :: ν, ⟨ha, hμ⟩, ⟨hb, hν⟩, ht => by
    obtain ⟨-, -, h3, -, h5, -⟩ := digit p q r a b t ha hb ht
    exact ⟨h5, rel_fwd_left p q _ ρ μ ν hμ hν h3⟩

/-- For two bosons this is the rule of `RMT.RSK.GrowthKnuth`. -/
theorem fwdC_bosons : ∀ (t : Nat) (ρ μ ν : Part),
    fwdC false false t ρ μ ν = GrowthKnuth.fwdC t ρ μ ν
  | t, r :: ρ, a :: μ, b :: ν => by
    simp only [fwdC, GrowthKnuth.fwdC, carry, fwdC_bosons _ ρ μ ν]
    congr 2; omega
  | _, [], _, _ => by simp [fwdC, GrowthKnuth.fwdC]
  | _, _ :: _, [], _ => by simp [fwdC, GrowthKnuth.fwdC]
  | _, _ :: _, _ :: _, [] => by simp [fwdC, GrowthKnuth.fwdC]

/-! ## The grid -/

section Grid

-- The parity of each row (`rp`) and each column (`cp`); `true` is a fermion.
variable (rp cp : Nat → Bool)

/-- The forward rule at square `(i, j)`, of the type given by the parities. -/
def F (i j : Nat) (ρ μ ν : Part) (x : Nat) : Part := fwdC (rp i) (cp j) x ρ μ ν

/-- The backward rule at square `(i, j)`. -/
def B (i j : Nat) (μ ν lam : Part) : Part × Nat := bwdC (rp i) (cp j) μ ν lam

/-- A filling compatible with the parities: entries `0` or `1` in mixed cells. -/
def Admissible (σ : Nat → Nat → Nat) : Prop := ∀ i j, CarryOK (rp i) (cp j) (σ i j)

variable (σ : Nat → Nat → Nat) (N : Nat)

/-- Room: no square of the `n × m` rectangle carries anything out of its last row. -/
def Room (n m : Nat) : Prop :=
  ∀ i j, i < n → j < m →
    carryOut (rp i) (cp j) (σ i j) (grow (F rp cp) (zeros N) σ i j)
      (grow (F rp cp) (zeros N) σ (i + 1) j) (grow (F rp cp) (zeros N) σ i (j + 1)) = 0

theorem length_fwdC (p q : Bool) : ∀ (t : Nat) (ρ μ ν : Part), ρ.length = μ.length →
    μ.length = ν.length → (fwdC p q t ρ μ ν).length = μ.length
  | _, [], [], [], _, _ => rfl
  | _, _ :: ρ, _ :: μ, _ :: ν, h1, h2 => by
    simp only [fwdC, List.length_cons]
    rw [length_fwdC p q _ ρ μ ν (by simpa using h1) (by simpa using h2)]
  | _, [], _ :: _, _, h1, _ => by simp at h1
  | _, _ :: _, [], _, h1, _ => by simp at h1
  | _, _ :: _, _ :: _, [], _, h2 => by simp at h2
  | _, [], [], _ :: _, _, h2 => by simp at h2

theorem length_grow : ∀ i j, (grow (F rp cp) (zeros N) σ i j).length = N
  | 0, j => by simp [grow_zero_left, zeros]
  | i + 1, 0 => by simp [grow_zero_right, zeros]
  | i + 1, j + 1 => by
    rw [grow_succ]
    simp only [F]
    rw [length_fwdC _ _ _ _ _ _ (by rw [length_grow i j, length_grow (i + 1) j])
      (by rw [length_grow (i + 1) j, length_grow i (j + 1)]), length_grow (i + 1) j]
termination_by i j => (i, j)

/-- Along row index `i` the shapes grow as the parity of row `i` says, and along column index
`j` as the parity of column `j` says. One recursion over the grid. -/
theorem rel_grow (hσ : Admissible rp cp σ) : ∀ i j,
    RelL (rp i) (grow (F rp cp) (zeros N) σ i j) (grow (F rp cp) (zeros N) σ (i + 1) j) ∧
    RelL (cp j) (grow (F rp cp) (zeros N) σ i j) (grow (F rp cp) (zeros N) σ i (j + 1))
  | i, j => by
    constructor
    · cases j with
      | zero => rw [grow_zero_right, grow_zero_right]; exact RelL.refl _ _
      | succ j =>
        rw [grow_succ]
        have h := rel_grow hσ i j
        exact rel_fwd_right _ _ _ _ _ _ h.1 h.2 (hσ i j)
    · cases i with
      | zero => rw [grow_zero_left, grow_zero_left]; exact RelL.refl _ _
      | succ i =>
        rw [grow_succ]
        have h := rel_grow hσ i j
        exact rel_fwd_left _ _ _ _ _ _ h.1 h.2 (hσ i j)
termination_by i j => (i, j)

/-- **Local invertibility** for an admissible parity-labelled filling with room. -/
theorem locallyInvertible (hσ : Admissible rp cp σ) (n m : Nat) (hroom : Room rp cp σ N n m) :
    LocallyInvertible (F rp cp) (B rp cp) (zeros N) σ n m := by
  intro i j hi hj
  have h := rel_grow rp cp σ N hσ i j
  simp only [B]
  rw [grow_succ]
  exact bwd_fwd _ _ _ _ _ _ h.1 h.2 (hσ i j) (hroom i j hi hj)

/-- **An admissible parity-labelled filling with room is determined by the outer edges of its
growth diagram.** -/
theorem eq_of_edges (τ : Nat → Nat → Nat) (hσ : Admissible rp cp σ) (hτ : Admissible rp cp τ)
    (n m : Nat) (hrσ : Room rp cp σ N n m) (hrτ : Room rp cp τ N n m)
    (htop : ∀ j, j ≤ m → grow (F rp cp) (zeros N) σ n j = grow (F rp cp) (zeros N) τ n j)
    (hright : ∀ i, i ≤ n → grow (F rp cp) (zeros N) σ i m = grow (F rp cp) (zeros N) τ i m) :
    ∀ i j, i < n → j < m → σ i j = τ i j :=
  GrowthGeneric.eq_of_edges (F rp cp) (B rp cp) _ σ τ n m
    (locallyInvertible rp cp σ N hσ n m hrσ) (locallyInvertible rp cp τ N hτ n m hrτ) htop hright

end Grid

end RMT.RSK.GrowthSuper
