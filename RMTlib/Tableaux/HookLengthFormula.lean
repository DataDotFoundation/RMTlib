import RMTlib.Tableaux.Hooks
import RMTlib.Tableaux.Lagrange

/-!
# The hook-length formula

`f^ν · H(ν) = |ν|!`, where `f^ν` counts standard Young tableaux of shape `ν` (paths `∅ → ν` in
Young's lattice, by the branching recursion `fSYT`) and `H(ν)` is the hook product.

Proof:
- Frobenius's identity (`RMT.frobenius`) puts `|ν|!/H(ν)` in the form
  `G(ν) = |ν|! ∏_{i<j}(ℓ_i − ℓ_j) / ∏ ℓ_i!`, with `ℓ_i = ν_i + N − 1 − i` (`G_mul_hookProd`).
- Removing a corner from row `k` lowers `ℓ_k` by one. It multiplies `G` by
  `ℓ_k ∏_{j≠k}(ℓ_k − ℓ_j − 1)/(ℓ_k − ℓ_j) / |ν|` (`G_removeBox`, via `vand_update`).
- At rows that are not corners this term vanishes (`term_eq_zero`).
- The sum over all rows is `Σℓ_k − N(N−1)/2 = |ν|` by the Lagrange identity
  (`RMT.Lagrange.lagrange_identity`). So `G` satisfies the branching recursion, and
  `f^ν = G(ν)` by induction (`fSYT_eq_G`).

With the bridge `‖hw_ν‖²_Fock = H(ν)` (`RMT.Bridge.fockQ_hw_eq_hookProd`), this gives
`f^ν/|ν|! = 1/‖hw_ν‖²_Fock`: the Plancherel weight is the inverse Fock norm.
-/

open Finset
open scoped Nat

namespace RMT

variable {N : ℕ}

/-- Remove the last box of row `i` (no check that this is a corner). -/
def removeBox (ν : Fin N → ℕ) (i : Fin N) : Fin N → ℕ :=
  Function.update ν i (ν i - 1)

/-- Row `i` ends in a removable corner. -/
def IsCorner (ν : Fin N → ℕ) (i : Fin N) : Bool :=
  0 < ν i && (if h : i.val + 1 < N then ν ⟨i.val + 1, h⟩ < ν i else true)

/-- The number of standard Young tableaux of shape `ν` (paths `∅ → ν` in Young's lattice), by the
branching recursion; `fuel ≥ |ν|`. -/
def fSYT : ℕ → (Fin N → ℕ) → ℕ
  | 0, ν => if ∑ i, ν i = 0 then 1 else 0
  | f + 1, ν => if ∑ i, ν i = 0 then 1 else
      ∑ i ∈ univ.filter (fun i => IsCorner ν i), fSYT f (removeBox ν i)

/-! ### The Vandermonde product under `x_k ↦ x_k − 1` -/

/-- The triangular Vandermonde product `∏_{i<j} (x_i − x_j)`. -/
def vand (x : Fin N → ℚ) : ℚ := ∏ i, ∏ j ∈ Ioi i, (x i - x j)

/-- A triangular product whose factors are `1` away from row and column `k`. -/
theorem tri_prod_eq (h : Fin N → Fin N → ℚ) (k : Fin N)
    (hh : ∀ i j, i < j → i ≠ k → j ≠ k → h i j = 1) :
    ∏ i, ∏ j ∈ Ioi i, h i j = (∏ j ∈ Ioi k, h k j) * ∏ i ∈ Iio k, h i k := by
  rw [← mul_prod_erase univ _ (mem_univ k)]
  congr 1
  have : ∀ i ∈ univ.erase k, ∏ j ∈ Ioi i, h i j = if i < k then h i k else 1 := by
    intro i hi
    have hik := ne_of_mem_erase hi
    split_ifs with hlt
    · refine prod_eq_single_of_mem k (mem_Ioi.mpr hlt) fun j hj hjk => ?_
      exact hh i j (mem_Ioi.mp hj) hik hjk
    · refine prod_eq_one fun j hj => ?_
      have := mem_Ioi.mp hj
      exact hh i j this hik (by rintro rfl; exact hlt this)
  rw [prod_congr rfl this, ← prod_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_erase, mem_univ, mem_Iio, and_true]
  exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩

theorem prod_Ioi_mul_prod_Iio (r : Fin N → ℚ) (k : Fin N) :
    (∏ j ∈ Ioi k, r j) * ∏ j ∈ Iio k, r j = ∏ j ∈ univ.erase k, r j := by
  rw [← prod_union (disjoint_left.mpr fun j h1 h2 =>
    lt_asymm (mem_Ioi.mp h1) (mem_Iio.mp h2))]
  congr 1
  ext j
  simp only [mem_union, mem_Ioi, mem_Iio, mem_erase, mem_univ, and_true]
  exact ⟨fun h => h.elim ne_of_gt ne_of_lt, fun h => (lt_or_gt_of_ne h).symm⟩

/-- Lowering `x_k` by one multiplies the Vandermonde product by
`∏_{j≠k} (x_k − x_j − 1)/(x_k − x_j)`. -/
theorem vand_update (x : Fin N → ℚ) (hx : Function.Injective x) (k : Fin N) :
    vand (Function.update x k (x k - 1)) =
      vand x * ∏ j ∈ univ.erase k, (x k - x j - 1) / (x k - x j) := by
  have hne : ∀ i j, i ≠ j → x i - x j ≠ 0 := fun i j h => sub_ne_zero.mpr (hx.ne h)
  have hV : vand x ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j hj =>
      hne i j (ne_of_lt (mem_Ioi.mp hj))
  set x' := Function.update x k (x k - 1) with hx'
  rw [mul_comm, ← div_eq_iff hV, vand, vand, ← prod_div_distrib]
  simp_rw [← prod_div_distrib]
  rw [tri_prod_eq (fun i j => (x' i - x' j) / (x i - x j)) k (fun i j hij hik hjk => by
    simp only [hx', Function.update_of_ne hik, Function.update_of_ne hjk]
    exact div_self (hne i j hij.ne)), ← prod_Ioi_mul_prod_Iio]
  congr 1
  · refine prod_congr rfl fun j hj => ?_
    simp only [hx', Function.update_self, Function.update_of_ne (ne_of_gt (mem_Ioi.mp hj))]
    ring_nf
  · refine prod_congr rfl fun j hj => ?_
    simp only [hx', Function.update_self, Function.update_of_ne (ne_of_lt (mem_Iio.mp hj))]
    rw [← neg_div_neg_eq]
    ring_nf

/-! ### Shifted parts and the Frobenius form of `|ν|!/H(ν)` -/

theorem ell_strictAnti {ν : Fin N → ℕ} (hν : Antitone ν) : StrictAnti (ell ν) := by
  intro i j hij
  have := hν hij.le
  have := j.isLt
  have : (i : ℕ) < j := hij
  simp only [ell]
  omega

/-- The shifted parts `ℓ_i = ν_i + N − 1 − i`, as rationals. -/
def ellQ (ν : Fin N → ℕ) (i : Fin N) : ℚ := ell ν i

theorem ellQ_injective {ν : Fin N → ℕ} (hν : Antitone ν) : Function.Injective (ellQ ν) :=
  fun i j h => (ell_strictAnti hν).injective (by
    have h' : ((ell ν i : ℕ) : ℚ) = ell ν j := h
    exact_mod_cast h')

theorem ell_removeBox_self {ν : Fin N → ℕ} {k : Fin N} (hk : 0 < ν k) :
    ell (removeBox ν k) k = ell ν k - 1 := by
  simp only [ell, removeBox, Function.update_self]
  omega

theorem ellQ_removeBox {ν : Fin N → ℕ} {k : Fin N} (hk : 0 < ν k) :
    ellQ (removeBox ν k) = Function.update (ellQ ν) k (ellQ ν k - 1) := by
  funext i
  by_cases h : i = k
  · subst h
    simp only [ellQ, Function.update_self, ell_removeBox_self hk]
    rw [Nat.cast_sub (by simp only [ell]; omega), Nat.cast_one]
  · simp only [ellQ, ell, removeBox, Function.update_of_ne h]

theorem sum_removeBox {ν : Fin N → ℕ} {k : Fin N} (hk : 0 < ν k) :
    ∑ i, removeBox ν k i + 1 = ∑ i, ν i := by
  rw [← add_sum_erase univ _ (mem_univ k), ← add_sum_erase univ ν (mem_univ k)]
  have : ∑ i ∈ univ.erase k, removeBox ν k i = ∑ i ∈ univ.erase k, ν i :=
    sum_congr rfl fun i hi => Function.update_of_ne (ne_of_mem_erase hi) _ _
  rw [this, removeBox, Function.update_self]
  omega

/-- `|ν|! · ∏_{i<j}(ℓ_i − ℓ_j) / ∏ ℓ_i!`, which is `|ν|!/H(ν)` by Frobenius's identity. -/
def G (ν : Fin N → ℕ) : ℚ := ((∑ i, ν i)! : ℚ) * vand (ellQ ν) / ∏ i, ((ell ν i)! : ℚ)

theorem vand_ellQ {ν : Fin N → ℕ} (hν : Antitone ν) :
    vand (ellQ ν) = ((∏ i, ∏ j ∈ Ioi i, (ν i - ν j + (j - i)) : ℕ) : ℚ) := by
  rw [vand, Nat.cast_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [Nat.cast_prod]
  refine prod_congr rfl fun j hj => ?_
  have hlt := ell_strictAnti hν (mem_Ioi.mp hj)
  have : ν i - ν j + (j - i) = ell ν i - ell ν j := by
    have hij : i < j := mem_Ioi.mp hj
    have : (i : ℕ) < j := hij
    have := hν hij.le
    have := j.isLt
    simp only [ell]
    omega
  rw [this, Nat.cast_sub hlt.le]
  rfl

theorem G_mul_hookProd {ν : Fin N → ℕ} (hν : Antitone ν) :
    G ν * hookProd ν = ((∑ i, ν i)! : ℚ) := by
  have hF : (hookProd ν : ℚ) * vand (ellQ ν) = ∏ i, ((ell ν i)! : ℚ) := by
    rw [vand_ellQ hν]
    exact_mod_cast frobenius ν hν
  have hP : (∏ i, ((ell ν i)! : ℚ)) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => by positivity
  rw [G, div_mul_eq_mul_div, div_eq_iff hP, ← hF]
  ring

/-- The branching ratio: removing a corner from row `k`. -/
theorem G_removeBox {ν : Fin N → ℕ} (hν : Antitone ν) {k : Fin N} (hk : 0 < ν k) :
    G (removeBox ν k) * ((∑ i, ν i : ℕ) : ℚ) =
      G ν * (ellQ ν k * ∏ j ∈ univ.erase k, (ellQ ν k - ellQ ν j - 1) / (ellQ ν k - ellQ ν j)) := by
  have hs := sum_removeBox hk
  have hellk : 0 < ell ν k := by simp only [ell]; omega
  have hfact : (∏ i, ((ell (removeBox ν k) i)! : ℚ)) * ellQ ν k = ∏ i, ((ell ν i)! : ℚ) := by
    rw [← mul_prod_erase univ _ (mem_univ k), ← mul_prod_erase univ (fun i => ((ell ν i)! : ℚ))
      (mem_univ k)]
    have : ∏ i ∈ univ.erase k, ((ell (removeBox ν k) i)! : ℚ) = ∏ i ∈ univ.erase k, ((ell ν i)! : ℚ) :=
      prod_congr rfl fun i hi => by
        simp only [ell, removeBox, Function.update_of_ne (ne_of_mem_erase hi)]
    rw [this, ell_removeBox_self hk, ellQ, ← Nat.mul_factorial_pred hellk.ne']
    push_cast
    ring
  have hP : (∏ i, ((ell (removeBox ν k) i)! : ℚ)) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => by positivity
  have hl : ellQ ν k ≠ 0 := by simp only [ellQ]; exact_mod_cast hellk.ne'
  rw [G, G, ellQ_removeBox hk, vand_update _ (ellQ_injective hν), ← hfact, ← hs,
    Nat.factorial_succ]
  push_cast
  field_simp

/-- At a row that is not a corner, the branching term vanishes. -/
theorem term_eq_zero {ν : Fin N → ℕ} (hν : Antitone ν) {k : Fin N} (hk : IsCorner ν k = false) :
    ellQ ν k * ∏ j ∈ univ.erase k, (ellQ ν k - ellQ ν j - 1) / (ellQ ν k - ellQ ν j) = 0 := by
  by_cases h : k.val + 1 < N
  · have hle := hν (show k ≤ ⟨k.val + 1, h⟩ from Fin.le_def.mpr (Nat.le_succ _))
    have heq : ν ⟨k.val + 1, h⟩ = ν k := by
      simp only [IsCorner, h, dif_pos, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hk
      omega
    refine mul_eq_zero_of_right _ (prod_eq_zero (i := ⟨k.val + 1, h⟩)
      (mem_erase.mpr ⟨fun e => by simp [Fin.ext_iff] at e, mem_univ _⟩) ?_)
    have : ell ν k = ell ν ⟨k.val + 1, h⟩ + 1 := by simp only [ell, heq]; omega
    simp only [ellQ, this]
    push_cast
    ring
  · have hk0 : ν k = 0 := by
      simp only [IsCorner, h, dif_neg, not_false_eq_true, Bool.and_true, decide_eq_false_iff_not] at hk
      omega
    refine mul_eq_zero_of_left ?_ _
    have : ell ν k = 0 := by simp only [ell]; omega
    simp [ellQ, this]

theorem removeBox_antitone {ν : Fin N → ℕ} (hν : Antitone ν) {k : Fin N}
    (hk : IsCorner ν k = true) : Antitone (removeBox ν k) ∧ 0 < ν k := by
  simp only [IsCorner, Bool.and_eq_true, decide_eq_true_eq] at hk
  refine ⟨fun a b hab => ?_, hk.1⟩
  simp only [removeBox, Function.update_apply]
  have := hν hab
  split_ifs with hb ha ha
  · omega
  · subst hb; omega
  · subst ha
    have hab' : (a : ℕ) < b := Fin.lt_def.mp (lt_of_le_of_ne hab (Ne.symm hb))
    have hb' : a.val + 1 < N := by have := b.isLt; omega
    rw [dif_pos hb'] at hk
    have := hν (show (⟨a.val + 1, hb'⟩ : Fin N) ≤ b from Fin.le_def.mpr (by simpa using hab'))
    simp only [decide_eq_true_eq] at hk
    omega
  · exact this

/-- **`f^ν = |ν|!/H(ν)`** in Frobenius form, by induction along the branching recursion, with the
Lagrange identity as the inductive step. -/
theorem fSYT_eq_G (n : ℕ) :
    ∀ ν : Fin N → ℕ, Antitone ν → ∑ i, ν i = n → (fSYT n ν : ℚ) = G ν := by
  induction n with
  | zero =>
    intro ν hν hs
    have h0 : ∀ i, ν i = 0 := fun i => (sum_eq_zero_iff.mp hs) i (mem_univ _)
    have hH : hookProd ν = 1 := by simp [hookProd, h0]
    have := G_mul_hookProd hν
    rw [hH, hs] at this
    simp only [Nat.cast_one, mul_one, Nat.factorial_zero] at this
    simp [fSYT, hs, this]
  | succ n ih =>
    intro ν hν hs
    rw [fSYT, if_neg (by omega), Nat.cast_sum]
    have hL := RMT.Lagrange.lagrange_identity N (ellQ ν) (ellQ_injective hν)
    have hell : ∑ i, ellQ ν i = ((n + 1 : ℕ) : ℚ) + ((N * (N - 1) / 2 : ℕ) : ℚ) := by
      simp only [ellQ, ← Nat.cast_sum]
      rw [← Nat.cast_add, ← hs, ← sum_fin_sub_one_sub, ← sum_add_distrib]
      rfl
    rw [hell, add_sub_cancel_right] at hL
    have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    calc ∑ i ∈ univ.filter (fun i => IsCorner ν i), (fSYT n (removeBox ν i) : ℚ)
        = ∑ i ∈ univ.filter (fun i => IsCorner ν i), G ν * (ellQ ν i *
            ∏ j ∈ univ.erase i, (ellQ ν i - ellQ ν j - 1) / (ellQ ν i - ellQ ν j)) / (n + 1 : ℕ) :=
          sum_congr rfl fun i hi => by
            obtain ⟨ha, hpos⟩ := removeBox_antitone hν (mem_filter.mp hi).2
            have := sum_removeBox hpos
            rw [ih _ ha (by omega), eq_div_iff hn, ← G_removeBox hν hpos, hs]
      _ = ∑ i, G ν * (ellQ ν i *
            ∏ j ∈ univ.erase i, (ellQ ν i - ellQ ν j - 1) / (ellQ ν i - ellQ ν j)) / (n + 1 : ℕ) :=
          sum_filter_of_ne fun i _ h => by
            by_contra hc
            exact h (by rw [term_eq_zero hν (by simpa using hc)]; simp)
      _ = G ν := by
          rw [← sum_div, ← mul_sum, hL]
          field_simp

/-- **The hook-length formula** `f^ν · H(ν) = |ν|!`. -/
theorem hook_length_formula (ν : Fin N → ℕ) (hν : Antitone ν) :
    fSYT (∑ i, ν i) ν * hookProd ν = (∑ i, ν i)! := by
  have h := G_mul_hookProd hν
  rw [← fSYT_eq_G _ ν hν rfl] at h
  exact_mod_cast h

end RMT
