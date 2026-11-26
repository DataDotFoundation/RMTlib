import RMTlib.Places.Tower
import Mathlib.Data.Nat.Choose.Cast

/-!
# Erdős's integer on the chain of lifts (RMTlib#171)

A model of the chain of lifts, not a statement about the condensed edition. Bertrand's content
lives in the size at `∞`, which the edition's chain never evaluates (RH-Dual's `bertrand-p1.md`).

* `hset_block`: a consecutive block `{s, …, s+m−1}` of Maya positions is the rectangle `s^m`, with
  `H = ∏_{j<m} (s+j)!/j!`;
* `ksMoment N k = ∏_{j<N} C(2k+j, k)/C(k+j, k)`, the Keating–Snaith moment; `ksMoment_one` is
  Erdős's `C(2k, k)`;
* `hset_shift_block`: **translating the block `{k, …, k+N−1}` by `k` multiplies `H` by
  `ksMoment N k · H`**, i.e. `M_N(k) = H((2k)^N) / H(k^N)^2`;
* `Tower.hset_above_succ_of_block`: **on the chain of lifts**, if the particle side is the block
  `{k, …, k+N−1}` and the lift has gap `k`, the step law reads
  `H(a⁺_{i+1}) = M_N(k) · H(a⁺_i)^2 · ℓ! / ∏ dist`. Erdős's integer (`N = 1`) and the
  Keating–Snaith moment are exactly the translation part `T` of the step, divided by `H(a⁺_i)`.
  The crossing particle `ℓ` (the `S` term) and the distances (the `V` term) are what one crossing
  per lift adds.

An exact search (`scripts/erdos_chain_search.py`) finds no tower, StepOK at every step, whose
factor ratios `factorInf (i+1) / factorInf i` are the Keating–Snaith ratios `C(2k+i,k)/C(k+i,k)`.
In rank 1 it finds only the factorial coincidences `k ≤ 3`. So Erdős's integer sits in the
translation part of a lift, not in whole-factor ratios.
-/

namespace RMT.ErdosChain

open Finset RMT.StringInsertion RMT.Tower

/-- **A consecutive block is a rectangle**: `H{s, …, s+m−1} = ∏_{j<m} (s+j)!/j!`. -/
theorem hset_block (s m : ℕ) :
    hset (Ico s (s + m)) = ∏ j ∈ range m, ((s + j).factorial : ℚ) / j.factorial := by
  induction m with
  | zero => simp [hset, fac, vd]
  | succ m ih =>
    have hI : Ico s (s + (m + 1)) = insert (s + m) (Ico s (s + m)) := by
      rw [← add_assoc, Nat.Ico_succ_right_eq_insert_Ico (by omega)]
    have hnot : s + m ∉ Ico s (s + m) := by simp
    rw [hI, hset_insert hnot, ih, prod_range_succ]
    have hd : ∏ x ∈ Ico s (s + m), (Nat.dist x (s + m) : ℚ) = m.factorial := by
      rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
      have : ∀ j ∈ range m, (Nat.dist (s + j) (s + m) : ℚ) = ((m - 1 - j) + 1 : ℕ) := by
        intro j hj
        have := mem_range.mp hj
        congr 1
        rw [Nat.dist_eq_sub_of_le (by omega)]
        omega
      rw [prod_congr rfl this, prod_range_reflect (fun j => (((j + 1 : ℕ)) : ℚ)) m]
      exact_mod_cast prod_range_add_one_eq_factorial m
    rw [hd]
    have : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
    field_simp

/-- **The Keating–Snaith moment** `M_N(k) = ∏_{j<N} C(2k+j, k)/C(k+j, k)`. -/
def ksMoment (N k : ℕ) : ℚ := ∏ j ∈ range N, ((2 * k + j).choose k : ℚ) / (k + j).choose k

/-- At rank `1` the moment is **Erdős's integer** `C(2k, k)`. -/
theorem ksMoment_one (k : ℕ) : ksMoment 1 k = (2 * k).choose k := by
  simp [ksMoment]

theorem ksMoment_eq (N k : ℕ) :
    ksMoment N k = ∏ j ∈ range N,
      ((2 * k + j).factorial : ℚ) * j.factorial / ((k + j).factorial : ℚ) ^ 2 := by
  refine prod_congr rfl fun j _ => ?_
  rw [Nat.cast_choose ℚ (by omega : k ≤ 2 * k + j), Nat.cast_choose ℚ (by omega : k ≤ k + j),
    show 2 * k + j - k = k + j by omega, show k + j - k = j by omega]
  have h1 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have h2 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have h3 : ((k + j).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- **`M_N(k) = H((2k)^N) / H(k^N)^2`**: translating the block `{k, …, k+N−1}` by `k`
multiplies `H` by `ksMoment N k · H`. -/
theorem hset_shift_block (N k : ℕ) :
    hset (shift (Ico k (k + N)) k) = ksMoment N k * hset (Ico k (k + N)) ^ 2 := by
  rw [hset_shift, hset_block, ksMoment_eq, prod_Ico_eq_prod_range, Nat.add_sub_cancel_left, sq,
    ← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [show k + j + k = 2 * k + j by ring]
  have h2 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have h3 : ((k + j).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- **Erdős's integer as a translation**: `H{2k} = C(2k, k) · H{k}^2`. -/
theorem hset_shift_singleton (k : ℕ) :
    hset (shift {k} k) = (2 * k).choose k * hset {k} ^ 2 := by
  have := hset_shift_block 1 k
  rw [ksMoment_one, show Ico k (k + 1) = {k} by simp] at this
  exact this

/-- **Erdős's integer on the chain of lifts.** If at level `i` the particle side is the block
`{k, …, k+N−1}` and the lift has gap `k`, the step multiplies `H(a⁺)` by the Keating–Snaith moment
times `H(a⁺)`, then inserts the crossing particle `ℓ`. -/
theorem _root_.RMT.Tower.hset_above_succ_of_block (T : RMT.Tower) {i : ℕ} {z : ℤ}
    (h : T.StepOK i z) {N k : ℕ} (hB : (T.cut i).1 = Ico k (k + N)) (hg : T.gap i = k) :
    hset (T.cut (i + 1)).1 =
      ksMoment N k * hset (T.cut i).1 ^ 2 * ((z + T.gap i - T.c).toNat.factorial : ℚ) /
        ∏ x ∈ shift (T.cut i).1 (T.gap i).toNat,
          (Nat.dist x (z + T.gap i - T.c).toNat : ℚ) := by
  have hn : (z + T.gap i - T.c).toNat ∉ shift (T.cut i).1 (T.gap i).toNat :=
    crossing_not_mem_shift_above h.hc h.hd h.one
  rw [T.cut_succ_fst h, hset_insert hn]
  congr 2
  rw [hB, hg, Int.toNat_natCast, hset_shift_block]

/-- **A block can't straddle the band** (#171, P1): a configuration containing every integer from
`a ≤ −c` to `b ≥ c` has a point in the band `(−c, c)` (namely `0`). So under StepOK, where the band
is empty at every level, the points that cross one by one are never a consecutive block on both sides
of the band. -/
theorem not_bandEmpty_of_Icc_subset {Y : Finset ℤ} {a b c : ℤ} (hc : 0 < c) (ha : a ≤ -c)
    (hb : c ≤ b) (hY : Icc a b ⊆ Y) : ¬ BandEmpty Y c := fun h => by
  have := h 0 (hY (mem_Icc.mpr ⟨by omega, by omega⟩))
  omega

end RMT.ErdosChain
