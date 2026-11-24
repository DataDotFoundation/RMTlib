import RMTlib.RSK.GrowthSuper

/-!
# The strip conditions of the parity-labelled growth diagram

`RMT.RSK.GrowthSuper` proves that its local rule is invertible using only *per-row* relations
between the shapes of a square (`Rel`). Along a bosonic index a shape should in fact grow by a
horizontal strip, and along a fermionic index by a vertical strip; both conditions link
neighbouring rows. This file proves that the forward rule preserves them, so that every shape of
the growth diagram is a partition and every edge is a strip of the parity of its index.

Shapes are padded lists `Part = List Nat`, row `0` first.

* `Partition l`: `l` is weakly decreasing.
* `HStrip a b`: `b / a` is a horizontal strip, `a_k ≤ b_k` and `b_k ≤ a_{k−1}`.
* `VStrip a b`: `b / a` is a vertical strip, `a_k ≤ b_k ≤ a_k + 1` and `b_k ≤ b_{k−1}`.
* `Strip p`: `HStrip` for a boson (`p = false`), `VStrip` for a fermion (`p = true`).

## Main results

* `digit₂`: the two-row identity. For rows `k − 1` and `k` of a square, any incoming carry
  allowed by `CarryOK`, and `ρ_k ≤ ρ_{k−1}`, the conditions linking the two rows pass from the
  edges `ρ → μ`, `ρ → ν` to the edges `μ → λ`, `ν → λ`. All four parity types at once.
* `strip_fwdC`: if `ρ` is a partition, `Strip p ρ μ`, `Strip q ρ ν` and the carry bound holds,
  then `Strip q μ λ` and `Strip p ν λ` for `λ = fwdC p q x ρ μ ν`, and `λ` is a partition.
* `strip_grow`: in the growth diagram of an admissible parity-labelled filling every shape is a
  partition, every edge along row index `i` is a `Strip (rp i)` and every edge along column
  index `j` a `Strip (cp j)`.

Neither result needs room (no carry out of the last row): a carry that falls off the bottom
does not break the strip conditions. For two bosons and for mixed squares, `ρ` being a partition
already follows from the strip hypotheses; for two fermions it is needed (the exhaustive check
in `scripts/growth_rules.py` finds squares that fail otherwise).

Mathlib-free.
-/

namespace RMT.RSK.GrowthSuper

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthGeneric (grow grow_zero_left grow_zero_right grow_succ)

/-! ## Partitions and strips -/

/-- A padded shape is a partition: its rows weakly decrease. -/
def Partition : Part → Prop
  | a :: b :: l => b ≤ a ∧ Partition (b :: l)
  | _ => True

/-- `b / a` is a horizontal strip: `a_k ≤ b_k` in every row, and `b_k ≤ a_{k−1}` for `k > 0`.
The two shapes have the same length. -/
def HStrip : Part → Part → Prop
  | [], [] => True
  | [a], [b] => a ≤ b
  | a :: a' :: as, b :: b' :: bs => a ≤ b ∧ b' ≤ a ∧ HStrip (a' :: as) (b' :: bs)
  | _, _ => False

/-- `b / a` is a vertical strip: `a_k ≤ b_k ≤ a_k + 1` in every row, and `b_k ≤ b_{k−1}` for
`k > 0`. The two shapes have the same length. -/
def VStrip : Part → Part → Prop
  | [], [] => True
  | [a], [b] => a ≤ b ∧ b ≤ a + 1
  | a :: a' :: as, b :: b' :: bs => (a ≤ b ∧ b ≤ a + 1) ∧ b' ≤ b ∧ VStrip (a' :: as) (b' :: bs)
  | _, _ => False

/-- The strip along an index of parity `p`: horizontal for a boson, vertical for a fermion. -/
def Strip : Bool → Part → Part → Prop
  | false => HStrip
  | true => VStrip

/-- The condition linking rows `k − 1` and `k` of a strip `b / a` of parity `p`, in terms of
`a_{k−1}`, `b_{k−1}` and `b_k`. -/
def Adj : Bool → Nat → Nat → Nat → Prop
  | false, a, _, b' => b' ≤ a
  | true, _, b, b' => b' ≤ b

@[simp] theorem strip_nil (p : Bool) : Strip p [] [] := by cases p <;> trivial

@[simp] theorem strip_single (p : Bool) (a b : Nat) : Strip p [a] [b] ↔ Rel p a b := by
  cases p <;> rfl

theorem strip_cons_cons (p : Bool) (a a' b b' : Nat) (as bs : Part) :
    Strip p (a :: a' :: as) (b :: b' :: bs) ↔
      Rel p a b ∧ Adj p a b b' ∧ Strip p (a' :: as) (b' :: bs) := by
  cases p <;> rfl

/-- A strip in the sense of `Strip` satisfies the per-row relations of `RMT.RSK.GrowthSuper`. -/
theorem Strip.relL {p : Bool} : ∀ {a b : Part}, Strip p a b → RelL p a b
  | [], [], _ => trivial
  | [_], [_], h => ⟨(strip_single _ _ _).1 h, trivial⟩
  | _ :: _ :: _, _ :: _ :: _, h => by
    rw [strip_cons_cons] at h
    exact ⟨h.1, Strip.relL h.2.2⟩
  | [], _ :: _, h | _ :: _, [], h | [_], _ :: _ :: _, h | _ :: _ :: _, [_], h => by
    cases p <;> simp [Strip, HStrip, VStrip] at h

theorem Strip.length_eq {p : Bool} {a b : Part} (h : Strip p a b) : a.length = b.length :=
  h.relL.length_eq

/-- A strip on a partition is a partition. -/
theorem Strip.partition {p : Bool} : ∀ {a b : Part}, Partition a → Strip p a b → Partition b
  | [], [], _, _ | [_], [_], _, _ => trivial
  | _ :: _ :: _, _ :: _ :: _, ha, h => by
    rw [strip_cons_cons] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨?_, Strip.partition ha.2 h3⟩
    have := h3.relL
    cases p <;> simp only [Rel, Adj, RelL] at h1 h2 this <;> have := ha.1 <;> omega
  | [], _ :: _, _, h | _ :: _, [], _, h | [_], _ :: _ :: _, _, h | _ :: _ :: _, [_], _, h => by
    cases p <;> simp [Strip, HStrip, VStrip] at h

/-- Every partition is a strip of either parity on itself. -/
theorem Strip.refl (p : Bool) : ∀ {a : Part}, Partition a → Strip p a a
  | [], _ => strip_nil p
  | [_], _ => (strip_single _ _ _).2 (by cases p <;> simp [Rel])
  | _ :: _ :: _, ha => (strip_cons_cons _ _ _ _ _ _ _).2
      ⟨by cases p <;> simp [Rel], by cases p <;> exact ha.1, Strip.refl p ha.2⟩

theorem partition_zeros : ∀ N, Partition (zeros N)
  | 0 | 1 => trivial
  | N + 2 => ⟨Nat.le_refl 0, partition_zeros (N + 1)⟩

/-! ## One square -/

/-- **The two-row identity.** For rows `k − 1` (values `r₁ a₁ b₁` of `ρ μ ν`) and `k` (values
`r₂ a₂ b₂`), with the per-row relations, the conditions linking the two rows on the edges
`ρ → μ` (parity `p`) and `ρ → ν` (parity `q`), `ρ_k ≤ ρ_{k−1}`, and any carry `t` into row
`k − 1` allowed by the carry bound, the forward rule produces `λ_{k−1} = l₁`, `λ_k = l₂`
satisfying the linking conditions on the edges `μ → λ` (parity `q`) and `ν → λ` (parity `p`). -/
theorem digit₂ (p q : Bool) (r₁ a₁ b₁ r₂ a₂ b₂ t : Nat) (hr : r₂ ≤ r₁)
    (ha₁ : Rel p r₁ a₁) (hb₁ : Rel q r₁ b₁) (ha₂ : Rel p r₂ a₂) (hb₂ : Rel q r₂ b₂)
    (ha : Adj p r₁ a₁ a₂) (hb : Adj q r₁ b₁ b₂) (ht : CarryOK p q t) :
    let l₁ := max a₁ b₁ + carry p q t r₁ a₁ b₁
    let t₂ := t + min a₁ b₁ - r₁ - carry p q t r₁ a₁ b₁
    let l₂ := max a₂ b₂ + carry p q t₂ r₂ a₂ b₂
    Adj q a₁ l₁ l₂ ∧ Adj p b₁ l₁ l₂ := by
  intro l₁ t₂ l₂
  -- `omega` case-splits the `min`s and `max`s itself once the parity type is fixed.
  cases p <;> cases q <;>
    simp only [l₁, t₂, l₂, carry, Rel, Adj, CarryOK, Bool.false_eq_true,
      Bool.true_eq_false, false_or, true_or] at ha₁ hb₁ ha₂ hb₂ ha hb ht ⊢ <;> omega

/-- The first row of the result. -/
theorem fwdC_cons (p q : Bool) (t r a b : Nat) (ρ μ ν : Part) :
    fwdC p q t (r :: ρ) (a :: μ) (b :: ν)
      = (max a b + carry p q t r a b) :: fwdC p q (t + min a b - r - carry p q t r a b) ρ μ ν :=
  rfl

/-- **The forward rule preserves the strip conditions.** If `ρ` is a partition, `μ / ρ` is a
strip of parity `p`, `ν / ρ` a strip of parity `q`, and the incoming carry satisfies the carry
bound, then `λ / μ` is a strip of parity `q` and `λ / ν` a strip of parity `p`, for
`λ = fwdC p q t ρ μ ν`. No hypothesis on the carry out of the last row is needed. -/
theorem strip_fwdC (p q : Bool) : ∀ (t : Nat) (ρ μ ν : Part), Partition ρ → Strip p ρ μ →
    Strip q ρ ν → CarryOK p q t →
    Strip q μ (fwdC p q t ρ μ ν) ∧ Strip p ν (fwdC p q t ρ μ ν)
  | _, [], [], [], _, _, _, _ => ⟨strip_nil q, strip_nil p⟩
  | t, [r], [a], [b], _, hμ, hν, ht => by
    obtain ⟨-, -, -, h4, h5, -⟩ := digit p q r a b t ((strip_single _ _ _).1 hμ)
      ((strip_single _ _ _).1 hν) ht
    exact ⟨(strip_single _ _ _).2 h5, (strip_single _ _ _).2 h4⟩
  | t, r₁ :: r₂ :: ρ, a₁ :: a₂ :: μ, b₁ :: b₂ :: ν, hρ, hμ, hν, ht => by
    rw [strip_cons_cons] at hμ hν
    obtain ⟨ha₁, ha, hμ'⟩ := hμ
    obtain ⟨hb₁, hb, hν'⟩ := hν
    obtain ⟨-, -, h3, h4, h5, -⟩ := digit p q r₁ a₁ b₁ t ha₁ hb₁ ht
    have ih := strip_fwdC p q _ (r₂ :: ρ) (a₂ :: μ) (b₂ :: ν) hρ.2 hμ' hν' h3
    have hr₂ := hμ'.relL.1
    have hb₂ := hν'.relL.1
    obtain ⟨d₁, d₂⟩ := digit₂ p q r₁ a₁ b₁ r₂ a₂ b₂ t hρ.1 ha₁ hb₁ hr₂ hb₂ ha hb ht
    rw [fwdC_cons] at ih
    rw [fwdC_cons, fwdC_cons]
    exact ⟨(strip_cons_cons _ _ _ _ _ _ _).2 ⟨h5, d₁, ih.1⟩,
      (strip_cons_cons _ _ _ _ _ _ _).2 ⟨h4, d₂, ih.2⟩⟩
  | _, [], _ :: _, _, _, hμ, _, _ | _, _ :: _, [], _, _, hμ, _, _
  | _, [_], _ :: _ :: _, _, _, hμ, _, _ | _, _ :: _ :: _, [_], _, _, hμ, _, _ => by
    cases p <;> simp [Strip, HStrip, VStrip] at hμ
  | _, [], [], _ :: _, _, _, hν, _ | _, [_], [_], [], _, _, hν, _
  | _, [_], [_], _ :: _ :: _, _, _, hν, _ | _, _ :: _ :: _, _ :: _ :: _, [], _, _, hν, _
  | _, _ :: _ :: _, _ :: _ :: _, [_], _, _, hν, _ => by
    cases q <;> simp [Strip, HStrip, VStrip] at hν

/-- The result of the forward rule on a partition with strips is a partition. -/
theorem partition_fwdC (p q : Bool) (t : Nat) (ρ μ ν : Part) (hρ : Partition ρ)
    (hμ : Strip p ρ μ) (hν : Strip q ρ ν) (ht : CarryOK p q t) :
    Partition (fwdC p q t ρ μ ν) :=
  Strip.partition (hμ.partition hρ) (strip_fwdC p q t ρ μ ν hρ hμ hν ht).1

/-! ## The grid -/

section Grid

variable (rp cp : Nat → Bool) (σ : Nat → Nat → Nat) (N : Nat)

/-- **The strip conditions on the whole growth diagram.** For an admissible parity-labelled
filling, every shape is a partition, the edge from `(i, j)` to `(i + 1, j)` is a strip of the
parity of row `i`, and the edge from `(i, j)` to `(i, j + 1)` a strip of the parity of column
`j`. No room hypothesis is needed. -/
theorem strip_grow (hσ : Admissible rp cp σ) : ∀ i j,
    Partition (grow (F rp cp) (zeros N) σ i j) ∧
    Strip (rp i) (grow (F rp cp) (zeros N) σ i j) (grow (F rp cp) (zeros N) σ (i + 1) j) ∧
    Strip (cp j) (grow (F rp cp) (zeros N) σ i j) (grow (F rp cp) (zeros N) σ i (j + 1))
  | i, j => by
    have hρ : Partition (grow (F rp cp) (zeros N) σ i j) := by
      cases i with
      | zero => rw [grow_zero_left]; exact partition_zeros N
      | succ i =>
        cases j with
        | zero => rw [grow_zero_right]; exact partition_zeros N
        | succ j =>
          have h := strip_grow hσ i j
          exact Strip.partition (h.2.1.partition h.1)
            (by rw [grow_succ]; exact (strip_fwdC _ _ _ _ _ _ h.1 h.2.1 h.2.2 (hσ i j)).1)
    refine ⟨hρ, ?_, ?_⟩
    · cases j with
      | zero => rw [grow_zero_right, grow_zero_right]; exact Strip.refl _ (partition_zeros N)
      | succ j =>
        have h := strip_grow hσ i j
        rw [grow_succ]
        exact (strip_fwdC _ _ _ _ _ _ h.1 h.2.1 h.2.2 (hσ i j)).2
    · cases i with
      | zero => rw [grow_zero_left, grow_zero_left]; exact Strip.refl _ (partition_zeros N)
      | succ i =>
        have h := strip_grow hσ i j
        rw [grow_succ]
        exact (strip_fwdC _ _ _ _ _ _ h.1 h.2.1 h.2.2 (hσ i j)).1
termination_by i j => (i, j)

/-- Every shape of the growth diagram of an admissible filling is a partition. -/
theorem partition_grow (hσ : Admissible rp cp σ) (i j : Nat) :
    Partition (grow (F rp cp) (zeros N) σ i j) :=
  (strip_grow rp cp σ N hσ i j).1

/-- The edges along row index `i` are strips of the parity of row `i`. -/
theorem strip_grow_row (hσ : Admissible rp cp σ) (i j : Nat) :
    Strip (rp i) (grow (F rp cp) (zeros N) σ i j) (grow (F rp cp) (zeros N) σ (i + 1) j) :=
  (strip_grow rp cp σ N hσ i j).2.1

/-- The edges along column index `j` are strips of the parity of column `j`. -/
theorem strip_grow_col (hσ : Admissible rp cp σ) (i j : Nat) :
    Strip (cp j) (grow (F rp cp) (zeros N) σ i j) (grow (F rp cp) (zeros N) σ i (j + 1)) :=
  (strip_grow rp cp σ N hσ i j).2.2

end Grid

end RMT.RSK.GrowthSuper
