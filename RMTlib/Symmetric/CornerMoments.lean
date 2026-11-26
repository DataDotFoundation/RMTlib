import RMTlib.Symmetric.Corners
import RMTlib.Tableaux.Pieri
import RMTlib.Tableaux.HookLengthFormula

/-!
# The low moments of the corner charge, and Fomin's form of the up/down operators

The corner charge of a partition `ν` (`RMT.Symmetric.Corners.charge`: `+1` at the contents of the
addable cells, `−1` at the contents of the removable cells) has the first three moments

  `Σ_u charge(u) = 1`,  `Σ_u charge(u) u = 0`,  `Σ_u charge(u) u² = 2|ν|`

(`sum_charge_one`, `sum_charge_id`, `sum_charge_sq`): `#add − #rem = 1`, `Σ_add c = Σ_rem c`,
`Σ_add c² − Σ_rem c² = 2|ν|`. So **for every affine `r`, `Σ_add r(c) − Σ_rem r(c) = r(0)`**
(`sum_charge_affine`), and conversely, if this holds for every partition then `r` is affine
(`affine_of_sum_charge`, `sum_charge_eq_iff_affine`): a single row and a single column already
force constant first differences.

## Genuine corners and the row window

The charge lives on `N` rows `ν : Fin N → ℕ`, with the boundary charge `+1` at `−N`. The genuine
corners of the `N`-row shape are the rows `i` where a box can be added (`RMT.IsAddable`, content
`ν_i − i`) or removed (`RMT.IsCorner`, content `ν_i − 1 − i`). They are the charge except at the
boundary: when all `N` rows are nonempty (`Full`), the addable cell in row `N`, of content `−N`, is
outside the window (`sum_corners_eq_sum_charge`). So for affine `r`

  `Σ_{i addable} r(ν_i − i) − Σ_{i removable} r(ν_i − 1 − i) = r(0) − [ν full] r(−N)`

(`sum_corners_affine`), which is `r(0)` for every partition of length `< N`.

## Fomin's form

Let `U` add a box with weight `1` and `D_r` remove a box `□` with weight `r(c(□))`, as linear maps
on finitely supported functions of `ν : Fin N → ℕ` (`up`, `down`). Off the diagonal the two orders
agree (`addable_corner_iff`: a box added in row `i` and a box removed in row `j ≠ i` commute), so

  `[D_r, U] e_ν = (Σ_add r − Σ_rem r) e_ν`   (`commutator_single`)

and, for affine `r`, `[D_r, U] e_ν = (r(0) − [ν full] r(−N)) e_ν` (`commutator_single_affine`).
For `ℓ(ν) < N` this is `r(0) e_ν`: `(U, D_r)` is a pair of dual graded graphs in Fomin's sense
with `[D, U] = r(0)` exactly when `r` is affine (`commutator_eq_iff_affine`). The boundary term
vanishes when `r(−N) = 0`: for `r = N + c` the `N`-row truncation is exact.

Transposition reflects the contents, `c ↦ −c`: `r ↦ r(−·)` is affine iff `r` is, with the same
`r(0)` (`affine_comp_neg`, `commutator_single_neg`).

## Two down operators

`D_r` is linear in `r` (`down_add`, `down_smul`), so `D_{a c + b} = a D_c + b D_1`
(`down_affine`) and `[D_r, D_s] = (a b' − a' b) [D_c, D_1]` (`down_comm_affine`), with
`[D_1, D_c] e_{(2)} = e_∅ ≠ 0` (`down_one_content_comm_row_two`).
-/

open Finset

noncomputable section

namespace RMT.Symmetric.Corners

variable {N M : ℕ} {R : Type*} [CommRing R]

/-! ## Summation by parts in any commutative ring -/

/-- **Summation by parts, additively, in any commutative ring.**
`Σ_u charge(u) g(u) = Σ_i (g(b_i + 1) − g(b_i)) + g(−N)`. -/
theorem sum_charge_mul {ν : Fin N → ℕ} (hν : Antitone ν) (hM : ∀ i, ν i ≤ M) (g : ℤ → R) :
    ∑ u ∈ window N M, (charge ν u : R) * g u =
      ∑ i, (g (maya ν i + 1) - g (maya ν i)) + g (-(N : ℤ)) := by
  have hterm : ∀ u, (charge ν u : R) * g u =
      (if u - 1 ∈ mayaSet ν then g u else 0) - (if u ∈ mayaSet ν then g u else 0) +
        (if u = -(N : ℤ) then g u else 0) := by
    intro u
    unfold charge
    split_ifs <;> push_cast <;> ring
  simp_rw [hterm]
  rw [sum_add_distrib, sum_sub_distrib, ← sum_filter, ← sum_filter, ← sum_filter]
  have e1 : (window N M).filter (fun u => u - 1 ∈ mayaSet ν) =
      univ.image (fun i => maya ν i + 1) := by
    ext u
    simp only [mem_filter, mayaSet, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨-, i, hi⟩; exact ⟨i, by omega⟩
    · rintro ⟨i, rfl⟩; exact ⟨maya_succ_mem hM i, i, by ring⟩
  have e2 : (window N M).filter (fun u => u ∈ mayaSet ν) = univ.image (maya ν) := by
    ext u
    simp only [mem_filter, mayaSet, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨i, rfl⟩; exact ⟨maya_mem hM i, i, rfl⟩
  have e3 : (window N M).filter (fun u => u = -(N : ℤ)) = {-(N : ℤ)} := by
    ext u; simp only [mem_filter, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨neg_mem_window, rfl⟩
  rw [e1, e2, e3, sum_singleton,
    sum_image fun i _ j _ h => maya_injective hν (by simpa using h),
    sum_image fun i _ j _ h => maya_injective hν h, sum_sub_distrib]

/-- `Σ_{i < n} (2i + 1) = n²`. -/
theorem sum_range_two_mul_add_one (n : ℕ) : ∑ i ∈ range n, (2 * (i : R) + 1) = (n : R) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-! ## The first three moments -/

/-- **`#add − #rem = 1`**: the total charge is `1`. -/
theorem sum_charge_one {ν : Fin N → ℕ} (hν : Antitone ν) (hM : ∀ i, ν i ≤ M) :
    ∑ u ∈ window N M, (charge ν u : R) = 1 := by
  simpa using sum_charge_mul (R := R) hν hM (fun _ => 1)

/-- **`Σ_add c = Σ_rem c`**: the first moment of the charge vanishes. -/
theorem sum_charge_id {ν : Fin N → ℕ} (hν : Antitone ν) (hM : ∀ i, ν i ≤ M) :
    ∑ u ∈ window N M, (charge ν u : R) * u = 0 := by
  rw [sum_charge_mul hν hM (fun u => (u : R))]
  simp

/-- **`Σ_add c² − Σ_rem c² = 2|ν|`**: the second moment of the charge is twice the size. -/
theorem sum_charge_sq {ν : Fin N → ℕ} (hν : Antitone ν) (hM : ∀ i, ν i ≤ M) :
    ∑ u ∈ window N M, (charge ν u : R) * (u : R) ^ 2 = 2 * ∑ i, (ν i : R) := by
  rw [sum_charge_mul hν hM (fun u => (u : R) ^ 2)]
  have h : ∀ i : Fin N, ((maya ν i + 1 : ℤ) : R) ^ 2 - ((maya ν i : ℤ) : R) ^ 2 =
      2 * (ν i : R) - (2 * ((i : ℕ) : R) + 1) := by
    intro i; simp only [maya]; push_cast; ring
  simp_rw [h]
  rw [sum_sub_distrib, ← mul_sum,
    Fin.sum_univ_eq_sum_range (fun i => 2 * (i : R) + 1) N, sum_range_two_mul_add_one]
  push_cast; ring

/-- **The charge against an affine function**: `Σ_u charge(u) (a u + b) = b`, i.e.
`Σ_add r(c) − Σ_rem r(c) = r(0)` for `r = a c + b`. -/
theorem sum_charge_affine {ν : Fin N → ℕ} (hν : Antitone ν) (hM : ∀ i, ν i ≤ M) (a b : R) :
    ∑ u ∈ window N M, (charge ν u : R) * (a * u + b) = b := by
  have h : ∀ u : ℤ, (charge ν u : R) * (a * u + b) = a * ((charge ν u : R) * u) + b * charge ν u :=
    fun u => by ring
  simp_rw [h]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_charge_id hν hM, sum_charge_one hν hM]
  ring

/-! ## The converse: only affine functions -/

/-- `r : ℤ → R` is affine. -/
def IsAffine (r : ℤ → R) : Prop := ∃ a b : R, ∀ u : ℤ, r u = a * u + b

/-- An affine `r` is `r(1) − r(0)` times `u` plus `r(0)`. -/
theorem IsAffine.eq {r : ℤ → R} (h : IsAffine r) (u : ℤ) : r u = (r 1 - r 0) * u + r 0 := by
  obtain ⟨a, b, hr⟩ := h
  rw [hr, hr 1, hr 0]; push_cast; ring

/-- Constant first differences make a function affine. -/
theorem isAffine_of_sub (r : ℤ → R) (d : R) (h : ∀ u : ℤ, r u - r (u - 1) = d) : IsAffine r := by
  refine ⟨d, r 0, fun u => ?_⟩
  induction u using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have := h (k + 1); simp only [add_sub_cancel_right] at this
    push_cast at ih ⊢; linear_combination this + ih
  | pred k ih => have := h (-k); push_cast at ih ⊢; linear_combination ih - this

/-- A row `(k)` on one row: `Σ_u charge(u) r(u) = r(k) − r(k − 1) + r(−1)`. -/
theorem sum_charge_row (k : ℕ) (r : ℤ → R) :
    ∑ u ∈ window 1 k, (charge (fun _ : Fin 1 => k) u : R) * r u = r k - r (k - 1) + r (-1) := by
  rw [sum_charge_mul (fun _ _ _ => le_rfl) (fun _ => le_rfl)]
  simp [maya]

/-- The column dipoles telescope: `Σ_{i < m} (r(1 − i) − r(−i)) = r(1) − r(1 − m)`. -/
theorem sum_column_dipoles (m : ℕ) (r : ℤ → R) :
    ∑ i : Fin m, (r (1 - (i : ℤ)) - r (-(i : ℤ))) = r 1 - r (1 - m) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r (1 - (i : ℤ)) - r (-(i : ℤ))) m]
  have : ∀ i ∈ range m, r (1 - (i : ℤ)) - r (-(i : ℤ)) =
      (fun j : ℕ => r (1 - (j : ℤ))) i - (fun j : ℕ => r (1 - (j : ℤ))) (i + 1) := by
    intro i _; simp only; push_cast; ring_nf
  rw [sum_congr rfl this, sum_range_sub']
  simp

/-- A column `(1^m)` on `m` rows: `Σ_u charge(u) r(u) = r(1) − r(1 − m) + r(−m)`. -/
theorem sum_charge_column (m : ℕ) (r : ℤ → R) :
    ∑ u ∈ window m 1, (charge (fun _ : Fin m => 1) u : R) * r u = r 1 - r (1 - m) + r (-(m : ℤ)) := by
  rw [sum_charge_mul (fun _ _ _ => le_rfl) (fun _ => le_rfl), ← sum_column_dipoles]
  simp only [maya, Nat.cast_one, sub_add_cancel]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  ring_nf

/-- **A row and a column force affinity**: if `r(k) − r(k − 1) + r(−1) = r(0)` for every row
`(k)` and `r(1) − r(1 − m) + r(−m) = r(0)` for every column `(1^m)`, then `r` is affine. -/
theorem affine_of_row_column (r : ℤ → R) (hrow' : ∀ k : ℕ, r k - r (k - 1) + r (-1) = r 0)
    (hcol' : ∀ m : ℕ, r 1 - r (1 - m) + r (-(m : ℤ)) = r 0) : IsAffine r := by
  have hrow : ∀ k : ℕ, r k - r (k - 1) = r 0 - r (-1) := fun k => by
    linear_combination hrow' k
  have hcol : ∀ m : ℕ, r (1 - m) - r (-(m : ℤ)) = r 1 - r 0 := fun m => by
    linear_combination -hcol' m
  have h01 : r 0 - r (-1) = r 1 - r 0 := by simpa using hcol 1
  refine isAffine_of_sub r (r 1 - r 0) fun u => ?_
  rcases le_or_gt u 0 with hu | hu
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, u = 1 - (m + 1 : ℕ) := ⟨(1 - u).toNat - 1, by omega⟩
    have := hcol (m + 1)
    push_cast at this ⊢
    rw [show (1 : ℤ) - (m + 1) - 1 = -(m + 1) by ring]
    exact this
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = k := ⟨u.toNat, by omega⟩
    rw [hrow, h01]

/-- **Only affine functions have `Σ_add r − Σ_rem r = r(0)` for every partition**: a row `(k)`
gives `r(k) − r(k − 1) = r(0) − r(−1)`, a column `(1^m)` gives `r(1 − m) − r(−m) = r(1) − r(0)`. -/
theorem affine_of_sum_charge (r : ℤ → R)
    (h : ∀ (N M : ℕ) (ν : Fin N → ℕ), Antitone ν → (∀ i, ν i ≤ M) →
      ∑ u ∈ window N M, (charge ν u : R) * r u = r 0) : IsAffine r := by
  refine affine_of_row_column r (fun k => ?_) (fun m => ?_)
  · rw [← sum_charge_row]; exact h 1 k _ (fun _ _ _ => le_rfl) (fun _ => le_rfl)
  · rw [← sum_charge_column]; exact h m 1 _ (fun _ _ _ => le_rfl) (fun _ => le_rfl)

/-- **`Σ_add r − Σ_rem r = r(0)` on every partition iff `r` is affine.** -/
theorem sum_charge_eq_iff_affine (r : ℤ → R) :
    (∀ (N M : ℕ) (ν : Fin N → ℕ), Antitone ν → (∀ i, ν i ≤ M) →
      ∑ u ∈ window N M, (charge ν u : R) * r u = r 0) ↔ IsAffine r := by
  refine ⟨affine_of_sum_charge r, fun hr N M ν hν hM => ?_⟩
  obtain ⟨a, b, hab⟩ := hr
  simp_rw [hab]
  rw [sum_charge_affine hν hM]
  simp

/-- **Transposition**: `c ↦ −c` preserves affinity, and `r(0)`. -/
theorem affine_comp_neg {r : ℤ → R} : IsAffine (fun u => r (-u)) ↔ IsAffine r := by
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨-a, b, fun u => by have := h (-u); simp only [neg_neg] at this; rw [this]; push_cast; ring⟩
  · rintro ⟨a, b, h⟩
    exact ⟨-a, b, fun u => by simp only; rw [h]; push_cast; ring⟩


/-! ## Genuine corners -/

/-- All `N` rows of `ν` are nonempty: the addable cell of row `N`, of content `−N`, falls outside
the `N`-row window. -/
def Full (ν : Fin N → ℕ) : Prop := ∀ i, 0 < ν i

instance (ν : Fin N → ℕ) : Decidable (Full ν) := by unfold Full; infer_instance

theorem isAddable_zero {m : ℕ} (ν : Fin (m + 1) → ℕ) : RMT.IsAddable ν 0 = true := by
  simp [RMT.IsAddable]

theorem isAddable_succ {m : ℕ} (ν : Fin (m + 1) → ℕ) (i : Fin m) :
    RMT.IsAddable ν i.succ = decide (ν i.succ < ν i.castSucc) := by
  simp only [RMT.IsAddable, Fin.val_succ, Nat.succ_pos, dite_eq_left]
  congr 3

theorem isCorner_castSucc {m : ℕ} (ν : Fin (m + 1) → ℕ) (i : Fin m) :
    RMT.IsCorner ν i.castSucc =
      (decide (0 < ν i.castSucc) && decide (ν i.succ < ν i.castSucc)) := by
  simp only [RMT.IsCorner, Fin.val_castSucc, add_lt_add_iff_right, Fin.is_lt, dite_eq_left]
  congr 3

theorem isCorner_last {m : ℕ} (ν : Fin (m + 1) → ℕ) :
    RMT.IsCorner ν (Fin.last m) = decide (0 < ν (Fin.last m)) := by
  simp [RMT.IsCorner]

theorem full_iff_last {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) :
    Full ν ↔ 0 < ν (Fin.last m) :=
  ⟨fun h => h _, fun h i => lt_of_lt_of_le h (hν (Fin.le_last i))⟩

/-- **The genuine corners against the rows.** The addable cells (content `ν_i − i`, row `i`
addable) minus the removable cells (content `ν_i − 1 − i`) are the row dipoles plus the boundary
`−N`, except when all rows are full:
`Σ_add g − Σ_rem g = Σ_i (g(b_i + 1) − g(b_i)) + [ν not full] g(−N)`. -/
theorem sum_corners_eq_rows {ν : Fin N → ℕ} (hν : Antitone ν) (g : ℤ → R) :
    (∑ i, if RMT.IsAddable ν i then g ((ν i : ℤ) - i) else 0) -
        (∑ i, if RMT.IsCorner ν i then g ((ν i : ℤ) - 1 - i) else 0) =
      ∑ i, (g (maya ν i + 1) - g (maya ν i)) + (if Full ν then 0 else g (-(N : ℤ))) := by
  classical
  cases N with
  | zero => simp [Full]
  | succ m =>
    have hA : (∑ i, if RMT.IsAddable ν i then g ((ν i : ℤ) - i) else 0) =
        ∑ i, g ((ν i : ℤ) - i) -
          ∑ i : Fin m, if ν i.succ = ν i.castSucc then g ((ν i.succ : ℤ) - i.succ) else 0 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ (fun i => g ((ν i : ℤ) - i)), isAddable_zero,
        ite_eq_left rfl, add_sub_assoc, ← sum_sub_distrib]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      have := hν (Fin.castSucc_le_succ i)
      rw [isAddable_succ]
      by_cases h : ν i.succ < ν i.castSucc
      · rw [ite_eq_left (by simpa using h), ite_eq_right (by omega)]; ring
      · rw [ite_eq_right (by simpa using h), ite_eq_left (by omega)]; ring
    have hR : (∑ i, if RMT.IsCorner ν i then g ((ν i : ℤ) - 1 - i) else 0) =
        ∑ i, g ((ν i : ℤ) - 1 - i) -
          (∑ i : Fin m, if ν i.succ = ν i.castSucc then g ((ν i.castSucc : ℤ) - 1 - i.castSucc)
            else 0) -
          (if ν (Fin.last m) = 0 then g (-((m + 1 : ℕ) : ℤ)) else 0) := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (fun i => g ((ν i : ℤ) - 1 - i)),
        isCorner_last]
      have hsum : ∀ i : Fin m, (if RMT.IsCorner ν i.castSucc then
            g ((ν i.castSucc : ℤ) - 1 - i.castSucc) else 0) =
          g ((ν i.castSucc : ℤ) - 1 - i.castSucc) -
            if ν i.succ = ν i.castSucc then g ((ν i.castSucc : ℤ) - 1 - i.castSucc) else 0 := by
        intro i
        have := hν (Fin.castSucc_le_succ i)
        rw [isCorner_castSucc]
        by_cases h : 0 < ν i.castSucc ∧ ν i.succ < ν i.castSucc
        · rw [ite_eq_left (by simpa using h), ite_eq_right (by omega)]; ring
        · rw [ite_eq_right (by simpa using h), ite_eq_left (by omega)]; ring
      simp_rw [hsum, sum_sub_distrib]
      by_cases h : ν (Fin.last m) = 0
      · rw [ite_eq_right (by simp [h]), ite_eq_left h, h]; simp only [Fin.val_last]; push_cast; ring_nf
      · rw [ite_eq_left (by simp; omega), ite_eq_right h]; ring
    have hmatch : (∑ i : Fin m, if ν i.succ = ν i.castSucc then g ((ν i.succ : ℤ) - i.succ) else 0)
        = ∑ i : Fin m, if ν i.succ = ν i.castSucc then
            g ((ν i.castSucc : ℤ) - 1 - i.castSucc) else 0 := by
      refine sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rw [h]; congr 1; simp only [Fin.val_succ, Fin.val_castSucc]; push_cast; ring
      · rfl
    rw [hA, hR, hmatch]
    have hm : ∀ i : Fin (m + 1), maya ν i + 1 = (ν i : ℤ) - i := fun i => by simp [maya]
    have hm' : ∀ i : Fin (m + 1), maya ν i = (ν i : ℤ) - 1 - i := fun i => by simp [maya]; ring
    simp_rw [hm, hm', sum_sub_distrib]
    by_cases h : ν (Fin.last m) = 0
    · rw [ite_eq_left h, ite_eq_right (show ¬ Full ν by rw [full_iff_last hν]; omega)]; ring
    · rw [ite_eq_right h, ite_eq_left ((full_iff_last hν).mpr (by omega))]; ring

/-- **The genuine corners against the charge**:
`Σ_add g − Σ_rem g = Σ_u charge(u) g(u) − [ν full] g(−N)`. -/
theorem sum_corners_eq_sum_charge {ν : Fin N → ℕ} (hν : Antitone ν) (hM : ∀ i, ν i ≤ M)
    (g : ℤ → R) :
    (∑ i, if RMT.IsAddable ν i then g ((ν i : ℤ) - i) else 0) -
        (∑ i, if RMT.IsCorner ν i then g ((ν i : ℤ) - 1 - i) else 0) =
      ∑ u ∈ window N M, (charge ν u : R) * g u - (if Full ν then g (-(N : ℤ)) else 0) := by
  rw [sum_corners_eq_rows hν, sum_charge_mul hν hM]
  split_ifs <;> ring

/-- **The corner identity for affine `r`**: `Σ_add r − Σ_rem r = r(0) − [ν full] r(−N)`, so
`r(0)` for every partition of length `< N`. -/
theorem sum_corners_affine {ν : Fin N → ℕ} (hν : Antitone ν) {r : ℤ → R} (hr : IsAffine r) :
    (∑ i, if RMT.IsAddable ν i then r ((ν i : ℤ) - i) else 0) -
        (∑ i, if RMT.IsCorner ν i then r ((ν i : ℤ) - 1 - i) else 0) =
      r 0 - (if Full ν then r (-(N : ℤ)) else 0) := by
  have hM : ∀ i, ν i ≤ univ.sup ν := fun i => le_sup (mem_univ i)
  obtain ⟨a, b, hab⟩ := hr
  rw [sum_corners_eq_sum_charge hν hM]
  simp_rw [hab]
  rw [sum_charge_affine hν hM]
  simp

/-! ## Fomin's form of the up and down operators -/

/-- `U e_ν = Σ_{i addable} e_{ν + e_i}`: add a box, weight `1`. -/
def upVec (ν : Fin N → ℕ) : (Fin N → ℕ) →₀ R :=
  ∑ i, if RMT.IsAddable ν i then Finsupp.single (RMT.addBox ν i) 1 else 0

/-- `D_r e_ν = Σ_{i removable} r(ν_i − 1 − i) e_{ν − e_i}`: remove a box `□` with weight
`r(c(□))`. -/
def downVec (r : ℤ → R) (ν : Fin N → ℕ) : (Fin N → ℕ) →₀ R :=
  ∑ i, if RMT.IsCorner ν i then Finsupp.single (RMT.removeBox ν i) (r ((ν i : ℤ) - 1 - i)) else 0

variable (N R) in
/-- **The up operator** `U` on finitely supported functions of `ν : Fin N → ℕ`. -/
def up : ((Fin N → ℕ) →₀ R) →ₗ[R] ((Fin N → ℕ) →₀ R) := Finsupp.linearCombination R upVec

variable (N) in
/-- **The down operator** `D_r` on finitely supported functions of `ν : Fin N → ℕ`. -/
def down (r : ℤ → R) : ((Fin N → ℕ) →₀ R) →ₗ[R] ((Fin N → ℕ) →₀ R) :=
  Finsupp.linearCombination R (downVec r)

theorem up_single (ν : Fin N → ℕ) : up N R (Finsupp.single ν 1) = upVec ν := by
  simp [up]

theorem down_single (r : ℤ → R) (ν : Fin N → ℕ) (c : R) :
    down N r (Finsupp.single ν c) = c • downVec r ν := by
  simp [down]

/-- **A box added in row `i` and a box removed in row `j ≠ i` commute**: the two orders are
allowed together. -/
theorem addable_corner_iff {ν : Fin N → ℕ} (hν : Antitone ν) {i j : Fin N} (hij : i ≠ j) :
    (RMT.IsAddable ν i && RMT.IsCorner (RMT.addBox ν i) j) =
      (RMT.IsCorner ν j && RMT.IsAddable (RMT.removeBox ν j) i) := by
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  rw [Bool.eq_iff_iff]
  by_cases hadj : (j : ℕ) + 1 = i
  · -- `j` is the row above `i`
    have hi : 0 < (i : ℕ) := by omega
    have hj : (j : ℕ) + 1 < N := by omega
    have e1 : (⟨(i : ℕ) - 1, by omega⟩ : Fin N) = j := Fin.ext (by simp; omega)
    have e2 : (⟨(j : ℕ) + 1, hj⟩ : Fin N) = i := Fin.ext (by simp; omega)
    have a := hν (show j ≤ i from Fin.le_def.mpr (by omega))
    simp only [RMT.IsAddable, RMT.IsCorner, RMT.addBox, RMT.removeBox, dite_eq_left hi, dite_eq_left hj,
      e1, e2, Function.update_self, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij),
      Bool.and_eq_true, decide_eq_true_eq]
    omega
  · -- the updates do not touch the neighbours that are compared
    by_cases hi : 0 < (i : ℕ) <;> by_cases hj : (j : ℕ) + 1 < N
    · have n1 : (⟨(i : ℕ) - 1, by omega⟩ : Fin N) ≠ j := fun h => hadj (by
        have := congrArg Fin.val h; simp at this; omega)
      have n2 : (⟨(j : ℕ) + 1, hj⟩ : Fin N) ≠ i := fun h => hadj (by
        have := congrArg Fin.val h; simpa using this)
      simp only [RMT.IsAddable, RMT.IsCorner, RMT.addBox, RMT.removeBox, dite_eq_left hi, dite_eq_left hj,
        Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij),
        Function.update_of_ne n1, Function.update_of_ne n2,
        Bool.and_eq_true, decide_eq_true_eq]
      tauto
    · have n1 : (⟨(i : ℕ) - 1, by omega⟩ : Fin N) ≠ j := fun h => hadj (by
        have := congrArg Fin.val h; simp at this; omega)
      simp only [RMT.IsAddable, RMT.IsCorner, RMT.addBox, RMT.removeBox, dite_eq_left hi, dite_eq_right hj,
        Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij),
        Function.update_of_ne n1,
        Bool.and_eq_true, decide_eq_true_eq]
      tauto
    · have n2 : (⟨(j : ℕ) + 1, hj⟩ : Fin N) ≠ i := fun h => hadj (by
        have := congrArg Fin.val h; simpa using this)
      simp only [RMT.IsAddable, RMT.IsCorner, RMT.addBox, RMT.removeBox, dite_eq_right hi, dite_eq_left hj,
        Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij),
        Function.update_of_ne n2, Bool.and_eq_true, decide_eq_true_eq]
      tauto
    · simp only [RMT.IsAddable, RMT.IsCorner, RMT.addBox, RMT.removeBox, dite_eq_right hi, dite_eq_right hj,
        Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij),
        Bool.and_eq_true, decide_eq_true_eq]
      tauto

theorem removeBox_addBox_comm {ν : Fin N → ℕ} {i j : Fin N} (hij : i ≠ j) :
    RMT.removeBox (RMT.addBox ν i) j = RMT.addBox (RMT.removeBox ν j) i := by
  funext k
  simp only [RMT.removeBox, RMT.addBox, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- **Fomin's form**: off the diagonal the two orders cancel, so the commutator is diagonal,
`[D_r, U] e_ν = (Σ_{add} r(c) − Σ_{rem} r(c)) e_ν`. -/
theorem commutator_single {ν : Fin N → ℕ} (hν : Antitone ν) (r : ℤ → R) :
    down N r (up N R (Finsupp.single ν 1)) - up N R (down N r (Finsupp.single ν 1)) =
      ((∑ i, if RMT.IsAddable ν i then r ((ν i : ℤ) - i) else 0) -
        (∑ i, if RMT.IsCorner ν i then r ((ν i : ℤ) - 1 - i) else 0)) • Finsupp.single ν 1 := by
  classical
  set T1 : Fin N → Fin N → (Fin N → ℕ) →₀ R := fun i j =>
    if RMT.IsAddable ν i && RMT.IsCorner (RMT.addBox ν i) j then
      Finsupp.single (RMT.removeBox (RMT.addBox ν i) j) (r ((ν j : ℤ) - 1 - j) +
        if i = j then r ((ν i : ℤ) - i) - r ((ν i : ℤ) - 1 - i) else 0)
    else 0 with hT1
  set T2 : Fin N → Fin N → (Fin N → ℕ) →₀ R := fun i j =>
    if RMT.IsCorner ν j && RMT.IsAddable (RMT.removeBox ν j) i then
      Finsupp.single (RMT.addBox (RMT.removeBox ν j) i) (r ((ν j : ℤ) - 1 - j))
    else 0 with hT2
  have h1 : down N r (up N R (Finsupp.single ν 1)) = ∑ i, ∑ j, T1 i j := by
    rw [up_single, upVec, map_sum]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : RMT.IsAddable ν i
    · rw [ite_eq_left hi, down_single, one_smul, downVec]
      refine sum_congr rfl fun j _ => ?_
      simp only [hT1, hi, Bool.true_and]
      split_ifs with hj hij
      · subst hij; congr 1; simp [RMT.addBox]
      · congr 1; simp [RMT.addBox, Function.update_of_ne (Ne.symm hij)]
      · rfl
    · rw [ite_eq_right hi, map_zero]
      exact (sum_eq_zero fun j _ => by simp [hT1, hi]).symm
  have h2 : up N R (down N r (Finsupp.single ν 1)) = ∑ i, ∑ j, T2 i j := by
    rw [sum_comm, down_single, one_smul, downVec, map_sum]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : RMT.IsCorner ν j
    · rw [ite_eq_left hj, ← Finsupp.smul_single_one, map_smul, up_single, upVec, smul_sum]
      refine sum_congr rfl fun i _ => ?_
      simp only [hT2, hj, Bool.true_and]
      split_ifs
      · rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      · rw [smul_zero]
    · rw [ite_eq_right hj, map_zero]
      exact (sum_eq_zero fun i _ => by simp [hT2, hj]).symm
  rw [h1, h2, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  have hdiag : ∀ i, ∑ j, (T1 i j - T2 i j) = T1 i i - T2 i i := by
    intro i
    refine sum_eq_single i (fun j _ hji => ?_) (by simp)
    simp only [hT1, hT2, ite_eq_right (Ne.symm hji), add_zero, addable_corner_iff hν (Ne.symm hji),
      removeBox_addBox_comm (Ne.symm hji)]
    exact sub_self _
  simp_rw [hdiag]
  rw [sum_smul]
  refine sum_congr rfl fun i _ => ?_
  simp only [hT1, hT2]
  by_cases ha : RMT.IsAddable ν i <;> by_cases hc : RMT.IsCorner ν i
  · have hc' := RMT.isCorner_addBox hν i
    have ha' := RMT.isAddable_removeBox hν (RMT.removeBox_antitone hν hc).2
    simp only [ha, hc, hc', ha', Bool.true_and, ite_true, RMT.removeBox_addBox,
      RMT.addBox_removeBox (RMT.removeBox_antitone hν hc).2,
      ← Finsupp.single_sub]
    rw [Finsupp.smul_single_one]; congr 1; ring
  · have hc' := RMT.isCorner_addBox hν i
    simp only [ha, hc, hc', Bool.true_and, Bool.false_and, ite_true, RMT.removeBox_addBox,
      ite_false, Bool.false_eq_true, sub_zero]
    rw [Finsupp.smul_single_one]; congr 1; ring
  · have ha' := RMT.isAddable_removeBox hν (RMT.removeBox_antitone hν hc).2
    simp only [ha, hc, ha', Bool.true_and, Bool.false_and, ite_true, ite_false, Bool.false_eq_true,
      RMT.addBox_removeBox (RMT.removeBox_antitone hν hc).2,
      zero_sub]
    rw [neg_smul, Finsupp.smul_single_one]
  · simp [ha, hc]

/-- **`[D_r, U] = r(0)` for affine `r`**, up to the boundary of the `N`-row window:
`[D_r, U] e_ν = (r(0) − [ν full] r(−N)) e_ν`. -/
theorem commutator_single_affine {ν : Fin N → ℕ} (hν : Antitone ν) {r : ℤ → R}
    (hr : IsAffine r) :
    down N r (up N R (Finsupp.single ν 1)) - up N R (down N r (Finsupp.single ν 1)) =
      (r 0 - if Full ν then r (-(N : ℤ)) else 0) • Finsupp.single ν 1 := by
  rw [commutator_single hν, sum_corners_affine hν hr]

/-- **`[D_r, U] e_ν = r(0) e_ν` for every partition of length `< N`**, `r` affine. -/
theorem commutator_single_of_not_full {ν : Fin N → ℕ} (hν : Antitone ν) (hfull : ¬ Full ν)
    {r : ℤ → R} (hr : IsAffine r) :
    down N r (up N R (Finsupp.single ν 1)) - up N R (down N r (Finsupp.single ν 1)) =
      r 0 • Finsupp.single ν 1 := by
  rw [commutator_single_affine hν hr, ite_eq_right hfull, sub_zero]

/-- **An exact window**: when `r(−N) = 0` (as for `r = N + c`), `[D_r, U] = r(0)` on every
`ν : Fin N → ℕ`, full or not. -/
theorem commutator_single_of_boundary {ν : Fin N → ℕ} (hν : Antitone ν) {r : ℤ → R}
    (hr : IsAffine r) (h0 : r (-(N : ℤ)) = 0) :
    down N r (up N R (Finsupp.single ν 1)) - up N R (down N r (Finsupp.single ν 1)) =
      r 0 • Finsupp.single ν 1 := by
  rw [commutator_single_affine hν hr, h0, ite_self, sub_zero]

/-- The column `(1^m)` padded with an empty row, on `m + 1` rows. -/
def paddedColumn (m : ℕ) : Fin (m + 1) → ℕ := fun i => if (i : ℕ) < m then 1 else 0

theorem paddedColumn_antitone (m : ℕ) : Antitone (paddedColumn m) := by
  intro a b hab
  have : (a : ℕ) ≤ b := hab
  simp only [paddedColumn]
  split_ifs <;> omega

theorem paddedColumn_not_full (m : ℕ) : ¬ Full (paddedColumn m) := fun h => by
  simpa [paddedColumn] using h (Fin.last m)

/-- **Fomin's form holds exactly for affine `r`**: `[D_r, U] e_ν = r(0) e_ν` on every partition
`ν` of length `< N`, for every `N`, iff `r` is affine. The converse uses the row `(k)` on two rows
and the column `(1^m)` on `m + 1` rows. -/
theorem commutator_eq_iff_affine [Nontrivial R] (r : ℤ → R) :
    (∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ¬ Full ν →
      down N r (up N R (Finsupp.single ν 1)) - up N R (down N r (Finsupp.single ν 1)) =
        r 0 • Finsupp.single ν 1) ↔ IsAffine r := by
  refine ⟨fun h => ?_, fun hr N ν hν hf => commutator_single_of_not_full hν hf hr⟩
  -- the scalar is the corner sum, which is the row sum plus the boundary
  have hc : ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ¬ Full ν →
      ∑ i, (r (maya ν i + 1) - r (maya ν i)) + r (-(N : ℤ)) = r 0 := by
    intro N ν hν hf
    have := congrArg (fun f => f ν) ((commutator_single hν r).symm.trans (h N ν hν hf))
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at this
    rwa [sum_corners_eq_rows hν, ite_eq_right hf] at this
  refine affine_of_row_column r (fun k => ?_) (fun m => ?_)
  · have hanti : Antitone (![k, 0] : Fin 2 → ℕ) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    have := hc 2 ![k, 0] hanti (fun hf => by simpa using hf 1)
    rw [← this]
    simp [Fin.sum_univ_two, maya]
    ring_nf
  · have := hc (m + 1) _ (paddedColumn_antitone m) (paddedColumn_not_full m)
    rw [← this, Fin.sum_univ_castSucc, ← sum_column_dipoles]
    simp only [paddedColumn, maya, Fin.val_castSucc, Fin.is_lt, ite_true, Fin.val_last,
      lt_irrefl, ite_false]
    push_cast
    ring_nf

/-! ## Linearity in the weight: two down operators -/

/-- The down operator is additive in the weight. -/
theorem down_add (r s : ℤ → R) : down N (r + s) = down N r + down N s := by
  refine Finsupp.lhom_ext' fun ν => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply, down_single,
    one_smul, downVec, Pi.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Finsupp.single_add]

/-- The down operator is homogeneous in the weight. -/
theorem down_smul (k : R) (r : ℤ → R) : down N (k • r) = k • down N r := by
  refine Finsupp.lhom_ext' fun ν => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.smul_apply, down_single,
    one_smul, downVec, Pi.smul_apply, smul_sum]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Finsupp.smul_single]

/-- **Every affine down operator is a combination of two**: `D_{a c + b} = a D_c + b D_1`, with
`D_1` Young's lattice's down operator and `D_c` the content-weighted one. -/
theorem down_affine (a b : R) :
    down N (fun u => a * u + b) = a • down N (fun u => (u : R)) + b • down N (fun _ => 1) := by
  rw [show (fun u : ℤ => a * u + b) = a • (fun u : ℤ => (u : R)) + b • (fun _ : ℤ => (1 : R)) by
    funext u; simp, down_add,
    down_smul, down_smul]

/-- **Two down operators commute up to a determinant**: for `r = a c + b`, `s = a' c + b'`,
`[D_r, D_s] = (a b' − a' b) [D_c, D_1]`. So down operators with non-proportional affine weights
(as `T` at `p` and `N + c` at `∞`) do not commute when `[D_c, D_1] ≠ 0`. -/
theorem down_comm_affine (a b a' b' : R) :
    down N (fun u => a * u + b) * down N (fun u => a' * u + b') -
        down N (fun u => a' * u + b') * down N (fun u => a * u + b) =
      (a * b' - a' * b) •
        (down N (fun u => (u : R)) * down N (fun _ => 1) -
          down N (fun _ => 1) * down N (fun u => (u : R))) := by
  rw [down_affine, down_affine]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
  module

/-- **`[D_1, D_c] ≠ 0`**: on the row `(2)`, `[D_1, D_c] e_{(2)} = e_∅` (one row). -/
theorem down_one_content_comm_row_two :
    (down 1 (fun _ => (1 : ℚ)) * down 1 (fun u => (u : ℚ)) -
        down 1 (fun u => (u : ℚ)) * down 1 (fun _ => (1 : ℚ))) (Finsupp.single ![2] 1) =
      Finsupp.single ![0] 1 := by
  have e1 : RMT.removeBox (![2] : Fin 1 → ℕ) 0 = ![1] := by
    funext i; fin_cases i; rfl
  have e2 : RMT.removeBox (![1] : Fin 1 → ℕ) 0 = ![0] := by
    funext i; fin_cases i; rfl
  have c2 : RMT.IsCorner (![2] : Fin 1 → ℕ) 0 = true := by decide
  have c1 : RMT.IsCorner (![1] : Fin 1 → ℕ) 0 = true := by decide
  have d2 : ∀ r : ℤ → ℚ, downVec r (![2] : Fin 1 → ℕ) = Finsupp.single ![1] (r 1) := by
    intro r; simp [downVec, c2, e1]
  have d1 : ∀ r : ℤ → ℚ, downVec r (![1] : Fin 1 → ℕ) = Finsupp.single ![0] (r 0) := by
    intro r; simp [downVec, c1, e2]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, down_single, one_smul, d2]
  simp [d1]

/-! ## Transposition -/

/-- **The ω-twin of Fomin's form.** The transpose weight `r(−·)` is affine iff `r` is, with the same
value at `0`: the commutator `[D_{r(−·)}, U] = r(0)` of the dual datum is the same scalar. -/
theorem commutator_single_neg {ν : Fin N → ℕ} (hν : Antitone ν) (hfull : ¬ Full ν)
    {r : ℤ → R} (hr : IsAffine r) :
    down N (fun u => r (-u)) (up N R (Finsupp.single ν 1)) -
        up N R (down N (fun u => r (-u)) (Finsupp.single ν 1)) =
      r 0 • Finsupp.single ν 1 := by
  rw [commutator_single_of_not_full hν hfull (affine_comp_neg.mpr hr), neg_zero]

end RMT.Symmetric.Corners
