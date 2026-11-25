import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import MeaningLib.Frame.Pattern
import Mathlib.Tactic.Ring

/-!
# The string-insertion law: the exact part

RMTlib#49 Ask 2, `docs/string-insertion.md`. For a finite Maya set `L ⊂ ℕ`:

* `fac L = ∏_{ℓ ∈ L} ℓ!` (the one-body weight at `∞`, `ρ_∞ = ℓ!`);
* `vd L = ∏_{ℓ < ℓ′ ∈ L} (ℓ′ − ℓ)` (the Vandermonde);
* `mutEn L S = ∏_{ℓ ∈ L, s ∈ S} |ℓ − s|` (the mutual energy).

By Frobenius (`RMT.frobenius`) the hook product is `H(λ) = fac L / vd L` at the Maya positions
`L = {λ_i + N − 1 − i}`. The exact identities:

* `vd_insert`: `vd (insert a L) = vd L · ∏_{ℓ ∈ L} |ℓ − a|`;
* `vd_union` (**insertion identity**, Vandermonde form): for disjoint `L`, `S`,
  `vd (L ∪ S) = vd L · vd S · mutEn L S`;
* `fac_union`: `fac (L ∪ S) = fac L · fac S`.

Hence `H(L ⊔ S) · mutEn L S = H(L) · H(S)`: each insertion changes `log H` by a self-energy minus a mutual
energy. Telescoping and the exact square rule are immediate (the result depends only on the set).
-/

namespace RMT.StringInsertion

open Finset

/-- `∏_{ℓ ∈ L} ℓ!`. -/
def fac (L : Finset ℕ) : ℕ := ∏ ℓ ∈ L, ℓ.factorial

/-- The Vandermonde `∏_{ℓ < ℓ′ ∈ L} (ℓ′ − ℓ)`. -/
def vd (L : Finset ℕ) : ℕ := ∏ x ∈ L, ∏ y ∈ L.filter (x < ·), (y - x)

/-- The mutual energy `∏_{ℓ ∈ L, s ∈ S} |ℓ − s|`. -/
def mutEn (L S : Finset ℕ) : ℕ := ∏ x ∈ L, ∏ s ∈ S, Nat.dist x s

theorem fac_union {L S : Finset ℕ} (h : Disjoint L S) : fac (L ∪ S) = fac L * fac S :=
  prod_union h

/-- Inserting one site multiplies the Vandermonde by its distances to the others. -/
theorem vd_insert {L : Finset ℕ} {a : ℕ} (ha : a ∉ L) :
    vd (insert a L) = vd L * ∏ x ∈ L, Nat.dist x a := by
  unfold vd
  rw [prod_insert ha]
  -- the row of `a`
  have hrow : ∏ y ∈ (insert a L).filter (a < ·), (y - a) = ∏ y ∈ L.filter (a < ·), (y - a) := by
    rw [filter_insert, if_neg (lt_irrefl a)]
  -- the other rows gain the factor `a − x` when `x < a`
  have hcol : ∀ x ∈ L, ∏ y ∈ (insert a L).filter (x < ·), (y - x) =
      (∏ y ∈ L.filter (x < ·), (y - x)) * (if x < a then a - x else 1) := by
    intro x hx
    rw [filter_insert]
    split_ifs with hxa
    · rw [prod_insert (fun h => ha (mem_filter.mp h).1), mul_comm]
    · rw [mul_one]
  rw [hrow, prod_congr rfl hcol, prod_mul_distrib]
  -- combine `∏_{x, a < x} (x − a) · ∏_{x < a} (a − x) = ∏_x |x − a|`
  have hsplit : (∏ y ∈ L.filter (a < ·), (y - a)) * ∏ x ∈ L, (if x < a then a - x else 1) =
      ∏ x ∈ L, Nat.dist x a := by
    rw [prod_filter, ← prod_mul_distrib]
    refine prod_congr rfl fun x hx => ?_
    have hxa : x ≠ a := fun h => ha (h ▸ hx)
    rcases lt_or_gt_of_ne hxa with h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos h, one_mul]
      unfold Nat.dist
      omega
    · rw [if_pos h, if_neg (not_lt.mpr h.le), mul_one]
      unfold Nat.dist
      omega
  calc (∏ y ∈ L.filter (a < ·), (y - a)) *
        ((∏ x ∈ L, ∏ y ∈ L.filter (x < ·), (y - x)) * ∏ x ∈ L, (if x < a then a - x else 1))
      = (∏ x ∈ L, ∏ y ∈ L.filter (x < ·), (y - x)) *
        ((∏ y ∈ L.filter (a < ·), (y - a)) * ∏ x ∈ L, (if x < a then a - x else 1)) := by ring
    _ = _ := by rw [hsplit]

/-- **The insertion identity** (Vandermonde form): `vd (L ∪ S) = vd L · vd S · mutEn L S` for disjoint
`L`, `S`. With `fac_union`, `H(L ⊔ S) · mutEn L S = H(L) · H(S)`. -/
@[frame_pattern]
theorem vd_union {L S : Finset ℕ} (h : Disjoint L S) : vd (L ∪ S) = vd L * vd S * mutEn L S := by
  induction S using Finset.induction_on with
  | empty => simp [vd, mutEn]
  | insert a S haS ih =>
    have hL : a ∉ L := fun haL => disjoint_left.mp h haL (mem_insert_self a S)
    have hdis : Disjoint L S := disjoint_of_subset_right (subset_insert a S) h
    have haLS : a ∉ L ∪ S := by simp [hL, haS]
    rw [union_insert, vd_insert haLS, ih hdis, vd_insert haS, prod_union hdis]
    unfold mutEn
    simp only [prod_insert haS]
    rw [prod_mul_distrib]
    ring

end RMT.StringInsertion
