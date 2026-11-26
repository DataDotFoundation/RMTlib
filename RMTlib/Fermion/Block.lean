import Mathlib

/-!
# Inserting a full block of Maya sites (lane BF, RMTlib#168; RH-Dual#257, candidate 1)

At both kinds of place, the condensed edition's theta lift inserts a **full block of consecutive
Maya sites** (RH-Dual's `bf-sites.md`, P1, P2 and P4):

* at a split finite place `w`, the Hecke polynomial gains the factor
  `qPochhammer q k X = ∏_{b<k} (1 − q^b X)` (`heckePolyOp_pairWeilTarget`);
* at `∞`, the parameter gains `doubledBlock k`, the block `{(k−1)/2, …, (1−k)/2}` (in `l = 2λ`), and the
  Casimir comparison carries its constant `∑_b (b − (k−1)/2)^2 = k(k^2−1)/12`
  (`IsMatch.centred_casimirValue_eq`).

Both are the **one-body weight of the full block** `∏_{b<k} φ(b)` (`RMT.Fermion.Maya.seaWeight`):
multiplicative with `φ_w(b) = 1 − q^b X` at `w`, additive with `φ_∞(b) = (b − (k−1)/2)^2` at `∞`.
The fermionic expansion is uniform across places:

* `prod_one_sub_eq_sum_configs`: `∏_{b<k} (1 − q^b X) = ∑_{S ⊆ block} (−X)^{|S|} q^{∑ S}`, a sum over
  the particle configurations `S` of the block, each weighted by the product of one-body weights of its
  particles. Grouped by particle number `d` this is the `e`-side generating function
  `∑_d (−X)^d e_d(1, q, …, q^{k−1})` (`prod_one_sub_eq_sum_esymm`). The bosonic twin
  `1/∏(1 − q^b X) = ∑_d X^d h_d(…)` occurs nowhere in the edition (RH-Dual, QB3).
* `sum_block_sq`: the additive block weight at `∞`, `∑_{b<k} (b − (k−1)/2)^2 = k(k^2−1)/12 = |ρ_k|^2`.

Per RH-Dual's verdict, this unifies the two places thinly: the shared argument is the block
telescoping and the shared content is "insert the trivial representation of `U(k)`". The subspace
count at `w` and the local correspondence at `∞` remain two separate arguments.
-/

open Finset

namespace RMT.Fermion.Block

variable {R : Type*} [CommRing R]

/-- **The block's weight is a sum over its particle configurations.** -/
theorem prod_one_sub_eq_sum_configs (q X : R) (k : ℕ) :
    ∏ b ∈ range k, (1 - q ^ b * X) =
      ∑ S ∈ (range k).powerset, (-X) ^ S.card * q ^ (∑ b ∈ S, b) := by
  have : ∀ b ∈ range k, (1 - q ^ b * X) = 1 + (-X) * q ^ b := fun b _ => by ring
  rw [prod_congr rfl this, prod_one_add]
  refine sum_congr rfl fun S _ => ?_
  rw [prod_mul_distrib, prod_const, prod_pow_eq_pow_sum]

/-- Grouped by particle number: `∏_{b<k} (1 − q^b X) = ∑_{d ≤ k} (−X)^d e_d(1, q, …, q^{k−1})`. -/
theorem prod_one_sub_eq_sum_esymm (q X : R) (k : ℕ) :
    ∏ b ∈ range k, (1 - q ^ b * X) =
      ∑ d ∈ range (k + 1), (-X) ^ d * ∑ S ∈ (range k).powersetCard d, q ^ (∑ b ∈ S, b) := by
  rw [prod_one_sub_eq_sum_configs, ← sum_fiberwise_of_maps_to (g := Finset.card)
    (t := range (k + 1)) (fun S hS => by
      rw [mem_range, Nat.lt_succ_iff]; simpa using card_le_card (mem_powerset.mp hS))]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_sum, powersetCard_eq_filter]
  refine sum_congr rfl fun S hS => ?_
  rw [(mem_filter.mp hS).2]

theorem sum_range_cast (k : ℕ) : ∑ b ∈ range k, (b : ℚ) = k * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_range_cast_sq (k : ℕ) : ∑ b ∈ range k, (b : ℚ) ^ 2 = (k - 1) * k * (2 * k - 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- **The additive block weight at `∞`**: `∑_{b<k} (b − (k−1)/2)^2 = k(k^2−1)/12`, the constant
`|ρ_k|^2` at the block ends in `IsMatch.centred_casimirValue_eq`. -/
theorem sum_block_sq (k : ℕ) :
    ∑ b ∈ range k, ((b : ℚ) - (k - 1) / 2) ^ 2 = (k : ℚ) * ((k : ℚ) ^ 2 - 1) / 12 := by
  have : ∀ b ∈ range k, ((b : ℚ) - (k - 1) / 2) ^ 2 =
      (b : ℚ) ^ 2 - (k - 1) * b + (k - 1) ^ 2 / 4 := fun b _ => by ring
  rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_range_cast_sq,
    sum_range_cast, sum_const, card_range, nsmul_eq_mul]
  ring

end RMT.Fermion.Block
