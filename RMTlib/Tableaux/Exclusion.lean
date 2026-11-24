import Mathlib

/-!
# The exclusion threshold in Theorem 3 of Dehaye (arXiv:1201.4478)

In Theorem 3 the pair `(κ, λ)` contributes `dim(λ, S_k(κ))`, which vanishes when `κ` and the
rotated transpose of `λ` overlap in the `k × k` square. This file proves that the first overlap
occurs at `|κ| + |λ| = 2k` (`two_mul_le_of_overlap`), and that `2k` is attained (`overlap_row`).
So every coefficient `c_M(k)` with `M < 2k` sums over *all* pairs.

Partitions in the `k × k` box are functions `Fin k → ℕ`, weakly decreasing and bounded by `k`.
-/

open Finset

namespace RMT

/-- The transpose of `lam` at `j`: the number of parts of `lam` larger than `j`. -/
def tr {k : ℕ} (lam : Fin k → ℕ) (j : ℕ) : ℕ := #{i : Fin k | j < lam i}

/-- `κ` and the rotated transpose of `lam` overlap in the `k × k` square. -/
def Overlap (k : ℕ) (kap lam : Fin k → ℕ) : Prop :=
  ∃ i : Fin k, k < kap i + tr lam (k - 1 - i)

theorem tr_le {k : ℕ} (lam : Fin k → ℕ) (j : ℕ) : tr lam j ≤ k := by
  unfold tr
  exact (card_filter_le _ _).trans (by simp)

theorem tr_antitone {k : ℕ} (lam : Fin k → ℕ) {j j' : ℕ} (h : j ≤ j') : tr lam j' ≤ tr lam j := by
  unfold tr
  exact card_le_card (by intro x; simp only [mem_filter, mem_univ, true_and]; omega)

/-- Counting the boxes of `lam` by columns. -/
theorem sum_eq_sum_tr {k : ℕ} (lam : Fin k → ℕ) (h : ∀ i, lam i ≤ k) :
    ∑ i, lam i = ∑ j ∈ range k, tr lam j := by
  have row : ∀ i, lam i = ∑ j ∈ range k, if j < lam i then 1 else 0 := by
    intro i
    rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
    have : (range k).filter (· < lam i) = range (lam i) := by
      ext j; simp only [mem_filter, mem_range]; have := h i; omega
    rw [this, card_range]
  calc ∑ i, lam i = ∑ i, ∑ j ∈ range k, (if j < lam i then 1 else 0) := sum_congr rfl fun i _ => row i
    _ = ∑ j ∈ range k, ∑ i, (if j < lam i then 1 else 0) := sum_comm
    _ = ∑ j ∈ range k, tr lam j := by
        refine sum_congr rfl fun j _ => ?_
        unfold tr
        rw [card_eq_sum_ones, sum_filter]

theorem sum_ge_of_antitone {k : ℕ} (kap : Fin k → ℕ) (hk : Antitone kap) (i : Fin k) :
    (i.val + 1) * kap i ≤ ∑ j, kap j := by
  calc (i.val + 1) * kap i = ∑ _j ∈ Iic i, kap i := by rw [sum_const, Fin.card_Iic, smul_eq_mul]
    _ ≤ ∑ j ∈ Iic i, kap j := sum_le_sum fun j hj => hk (mem_Iic.mp hj)
    _ ≤ ∑ j, kap j := sum_le_sum_of_subset (subset_univ _)

theorem sum_tr_ge {k : ℕ} (lam : Fin k → ℕ) (i : Fin k) :
    (k - i.val) * tr lam (k - 1 - i) ≤ ∑ j ∈ range k, tr lam j := by
  calc (k - i.val) * tr lam (k - 1 - i) = ∑ _j ∈ range (k - i.val), tr lam (k - 1 - i) := by
        rw [sum_const, card_range, smul_eq_mul]
    _ ≤ ∑ j ∈ range (k - i.val), tr lam j :=
        sum_le_sum fun j hj => tr_antitone lam (j := j) (j' := k - 1 - i) (by have := mem_range.mp hj; omega)
    _ ≤ ∑ j ∈ range k, tr lam j := sum_le_sum_of_subset (by intro x hx; simp only [mem_range] at hx ⊢; omega)

/-- The arithmetic core: with `a + b > k`, `a, b ≤ k` and `0 ≤ i < k`,
`(i+1) a + (k-i) b ≥ 2k`. -/
theorem arith_core (k i a b : ℤ) (hi0 : 0 ≤ i) (hik : i < k) (ha : a ≤ k) (hb : b ≤ k)
    (h : k < a + b) : 2 * k ≤ (i + 1) * a + (k - i) * b := by
  have hab : k + 1 ≤ a + b := by omega
  rcases le_total (i + 1) (k - i) with hle | hle
  · nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 hle),
      mul_le_mul_of_nonneg_left hab (show (0 : ℤ) ≤ k - i by omega),
      mul_nonneg hi0 (show (0 : ℤ) ≤ k - 1 by omega)]
  · nlinarith [mul_le_mul_of_nonneg_left hb (sub_nonneg.2 hle),
      mul_le_mul_of_nonneg_left hab (show (0 : ℤ) ≤ i + 1 by omega),
      mul_nonneg (show (0 : ℤ) ≤ k - i - 1 by omega) (show (0 : ℤ) ≤ k - 1 by omega)]

/-- **Exclusion threshold.** If `κ` and the rotated transpose of `λ` overlap in the `k × k`
square, then `|κ| + |λ| ≥ 2k`. -/
theorem two_mul_le_of_overlap {k : ℕ} (kap lam : Fin k → ℕ) (hk : Antitone kap)
    (hkb : ∀ i, kap i ≤ k) (hlb : ∀ i, lam i ≤ k) (h : Overlap k kap lam) :
    2 * k ≤ ∑ i, kap i + ∑ i, lam i := by
  obtain ⟨i, hi⟩ := h
  have h1 := sum_ge_of_antitone kap hk i
  have h2 := sum_tr_ge lam i
  rw [← sum_eq_sum_tr lam hlb] at h2
  have ha := hkb i
  have hb := tr_le lam (k - 1 - i)
  have hik := i.isLt
  have key := arith_core k i.val (kap i) (tr lam (k - 1 - i)) (by positivity) (by exact_mod_cast hik)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hi)
  have ht : ((k - i.val : ℕ) : ℤ) = (k : ℤ) - i.val := by push_cast [Nat.cast_sub hik.le]; ring
  zify at h1 h2
  rw [ht] at h2
  linarith

/-- The threshold is attained: two full rows of length `k` overlap, with `|κ| + |λ| = 2k`. -/
theorem overlap_row {k : ℕ} (hk : 0 < k) :
    Overlap k (fun i => if i.val = 0 then k else 0) (fun i => if i.val = 0 then k else 0) := by
  refine ⟨⟨0, hk⟩, ?_⟩
  simp only [ite_true]
  have : 0 < tr (fun i : Fin k => if i.val = 0 then k else 0) (k - 1 - 0) := by
    unfold tr
    refine card_pos.mpr ⟨⟨0, hk⟩, ?_⟩
    simp only [mem_filter, mem_univ, true_and, ite_true]
    omega
  omega

end RMT
