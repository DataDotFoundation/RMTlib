import RMTlib.Moments.Theorem3UN

/-!
# Theorem 3 of Dehaye for U(N): the coefficients `M = 0` and `M = 1`, for every `k`

The statement `RMT.UN.Theorem3` (`RMTlib/Moments/Theorem3UN.lean`) is proved here for the two
leading coefficients and every `k`:

* `RMT.UN.theorem3_zero`: `c_0(k) = d_∅∅ · dim(∅, k×k)/(k²)! = f^{k×k}/(k²)!`, which is the
  Keating–Snaith constant `1/∏(i + j − 1)` by the hook-length formula
  (`RMT.hookLengthSquare_holds`).
* `RMT.UN.theorem3_one`: `c_1(k) = (d_{□∅} · dim(∅, S_k(□)) + d_{∅□} · dim(□, k×k))/(k² − 1)!`
  with `d_{□∅} = d_{∅□} = k/2` (`g'(0) = 1/2`, `k` cells per row and per column) and both path
  counts equal to `f^{k×k}`; this is `k³/∏(i + j − 1) = Σ(i + j − 1)/∏(i + j − 1)`.

Ingredients:
* In degree ≤ 1 the Vandermonde expansion keeps only `σ = τ = 1` (`dCoef_firstRow`, via
  `perm_eq_one_of_le`): a permutation that moves nothing down is the identity.
* `S_k(∅) = k × k` and `S_k(□) = k × k` minus its corner (`S_zero`, `S_single`); in general
  `S_k(κ)` is complementary to `κ` in the sense of Lemma 6 (`complementary_S`).
* `dim(∅, μ) = f^μ` and `dim(□, μ) = f^μ` for `μ ≠ ∅` (`skewDim_zero_left`, `skewDim_single`).
-/

open Finset
open scoped Nat

namespace RMT.UN

/-! ### The kernel `g(u) = u/(1 − e^{−u})` -/

theorem length_gTable (n : ℕ) : (gTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gTable, ih]

theorem gTable_reverse_getD (n : ℕ) : ∀ m ≤ n, (gTable n).reverse.getD m 0 = gCoeff m := by
  induction n with
  | zero => intro m hm; obtain rfl : m = 0 := by omega
            rfl
  | succ n ih =>
    intro m hm
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · rw [gTable, List.reverse_cons, List.getD_append _ _ _ _ (by simp [length_gTable]; omega)]
      exact ih m (by omega)
    · obtain rfl : m = n + 1 := by omega
      rw [gTable, List.reverse_cons, List.getD_append_right _ _ _ _ (by simp [length_gTable])]
      simp [length_gTable, gCoeff, gTable]

theorem gCoeff_zero : gCoeff 0 = 1 := rfl

theorem gCoeff_one : gCoeff 1 = 1 / 2 := by
  simp [gCoeff, gTable, hCoeff]; norm_num

theorem gFun_zero (D : ℕ) : gFun D 0 = 1 := by
  simp only [gFun, gLookup]; rw [gTable_reverse_getD D 0 (Nat.zero_le _), gCoeff_zero]

theorem gFun_one {D : ℕ} (hD : 1 ≤ D) : gFun D 1 = 1 / 2 := by
  simp only [gFun, gLookup]; rw [gTable_reverse_getD D 1 hD, gCoeff_one]

/-! ### Coefficients of `∏ g(a_i − b_j)` in degrees 0 and 1 -/

variable {k : ℕ} (g : ℕ → ℚ)

theorem expRange_zero (b : Bool) : expRange b 0 = {0} := by
  cases b <;> simp [expRange]

theorem update_zero (i : Fin k) : Function.update (0 : Fin k → ℕ) i 0 = 0 :=
  Function.update_eq_self _ _

theorem update_single_zero (i : Fin k) : Function.update (Pi.single i 1 : Fin k → ℕ) i 0 = 0 := by
  ext j; by_cases h : j = i <;> simp [h]

theorem update_single_one (i : Fin k) :
    Function.update (Pi.single i 1 : Fin k → ℕ) i 1 = Pi.single i 1 := by
  ext j; by_cases h : j = i <;> simp [h]

theorem update_single_ne {i c : Fin k} (h : c ≠ i) :
    Function.update (Pi.single i 1 : Fin k → ℕ) c 0 = Pi.single i 1 := by
  ext j; by_cases h' : j = c <;> simp [h', h]

theorem prodCoef_zero (hg : g 0 = 1) (cs : List (Fin k × Fin k)) : prodCoef g cs 0 0 = 1 := by
  induction cs with
  | nil => simp [prodCoef]
  | cons c cs ih => simp [prodCoef, expRange_zero, wt, hg, ih]

set_option linter.unusedSimpArgs false in
theorem prodCoef_single_left (hg : g 0 = 1) (i : Fin k) (cs : List (Fin k × Fin k)) :
    prodCoef g cs (Pi.single i 1) 0 = (cs.countP fun c => c.1 == i) * g 1 := by
  induction cs with
  | nil =>
    have : ¬ ∀ i', (Pi.single i 1 : Fin k → ℕ) i' = 0 := fun h => by simpa using h i
    simp [prodCoef, this]
  | cons c cs ih =>
    by_cases hc : c.1 = i
    · subst hc
      cases hL : cs.any (fun d => d.1 == c.1)
      · have hcnt : (cs.countP fun d => d.1 == c.1) = 0 := by
          rw [List.countP_eq_zero]; intro d hd hd'
          have := List.any_eq_false.mp hL d hd; simp_all
        simp [prodCoef, expRange, hL, expRange_zero, wt, hg, List.countP_cons, hcnt,
          prodCoef_zero g hg, update_zero, update_single_zero, update_single_one]
      · simp [prodCoef, expRange, hL, expRange_zero, wt, hg, List.countP_cons, sum_range_succ,
          prodCoef_zero g hg, update_zero, update_single_zero, update_single_one, ih]
        ring
    · have h0 : (Pi.single i 1 : Fin k → ℕ) c.1 = 0 := by simp [hc]
      simp [prodCoef, h0, expRange_zero, wt, hg, List.countP_cons, hc, ih, update_zero, update_single_ne hc]

set_option linter.unusedSimpArgs false in
theorem prodCoef_single_right (hg : g 0 = 1) (j : Fin k) (cs : List (Fin k × Fin k)) :
    prodCoef g cs 0 (Pi.single j 1) = (cs.countP fun c => c.2 == j) * (-g 1) := by
  induction cs with
  | nil =>
    have : ¬ ∀ j', (Pi.single j 1 : Fin k → ℕ) j' = 0 := fun h => by simpa using h j
    simp [prodCoef, this]
  | cons c cs ih =>
    by_cases hc : c.2 = j
    · subst hc
      cases hL : cs.any (fun d => d.2 == c.2)
      · have hcnt : (cs.countP fun d => d.2 == c.2) = 0 := by
          rw [List.countP_eq_zero]; intro d hd hd'
          have := List.any_eq_false.mp hL d hd; simp_all
        simp [prodCoef, expRange, hL, expRange_zero, wt, hg, List.countP_cons, hcnt,
          prodCoef_zero g hg, update_zero, update_single_zero, update_single_one]
      · simp [prodCoef, expRange, hL, expRange_zero, wt, hg, List.countP_cons, sum_range_succ,
          prodCoef_zero g hg, update_zero, update_single_zero, update_single_one, ih]
        ring
    · have h0 : (Pi.single j 1 : Fin k → ℕ) c.2 = 0 := by simp [hc]
      simp [prodCoef, h0, expRange_zero, wt, hg, List.countP_cons, hc, ih, update_zero, update_single_ne hc]

theorem countP_finRange (j : Fin k) : ((List.finRange k).countP fun x => x == j) = 1 :=
  List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange j)

theorem countP_cells_fst (i : Fin k) : ((cells k).countP fun c => c.1 == i) = k := by
  simp only [cells, List.countP_flatMap, List.countP_map, Function.comp_def]
  rw [← Fin.sum_univ_def]
  have : ∀ x : Fin k, ((List.finRange k).countP fun _ => x == i) = if x = i then k else 0 := by
    intro x; by_cases h : x = i <;> simp [h]
  simp [this]

theorem countP_cells_snd (j : Fin k) : ((cells k).countP fun c => c.2 == j) = k := by
  simp [cells, List.countP_flatMap, List.countP_map, Function.comp_def, countP_finRange]

/-! ### Only `σ = τ = 1` survives the Vandermonde expansion in low degree -/

theorem shiftExp_apply (κ : Fin k → ℕ) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    shiftExp κ σ i = κ i + ((σ i : ℕ) : ℤ) - (i : ℕ) := by
  have := i.isLt
  have := (σ i).isLt
  simp only [shiftExp, delta]
  omega

/-- A permutation of `Fin k` that moves nothing down is the identity. -/
theorem perm_eq_one_of_le (σ : Equiv.Perm (Fin k)) (h : ∀ i : Fin k, (i : ℕ) ≤ σ i) : σ = 1 := by
  have hs : ∑ i, ((σ i : Fin k) : ℕ) = ∑ i : Fin k, (i : ℕ) := Equiv.sum_comp σ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp hs.symm
  ext i
  simpa using (this i (mem_univ _)).symm

/-- `κ` vanishes off the first row. -/
def FirstRow (κ : Fin k → ℕ) : Prop := ∀ i : Fin k, (i : ℕ) ≠ 0 → κ i = 0

theorem exists_neg_shiftExp {κ : Fin k → ℕ} (hκ : FirstRow κ) {σ : Equiv.Perm (Fin k)}
    (hσ : σ ≠ 1) : ¬ ∀ i, 0 ≤ shiftExp κ σ i := by
  intro h
  refine hσ (perm_eq_one_of_le σ fun (i : Fin k) => ?_)
  have := h i
  rw [shiftExp_apply] at this
  by_cases hi : (i : ℕ) = 0
  · omega
  · rw [hκ i hi] at this; omega

/-- For `κ`, `λ` in the first row, `d_κλ = (−1)^{|λ|} [a^κ b^λ] f~`. -/
theorem dCoef_firstRow (F : (Fin k → ℕ) → (Fin k → ℕ) → ℚ) {κ lam : Fin k → ℕ}
    (hκ : FirstRow κ) (hl : FirstRow lam) : dCoef F κ lam = (-1) ^ (∑ i, lam i) * F κ lam := by
  unfold dCoef
  congr 1
  rw [Finset.sum_eq_single 1, Finset.sum_eq_single 1]
  · simp [coefZ, shiftExp_apply]
  · intro τ _ hτ
    simp [coefZ, exists_neg_shiftExp hl hτ]
  · simp
  · intro σ _ hσ
    refine Finset.sum_eq_zero fun τ _ => ?_
    simp [coefZ, exists_neg_shiftExp hκ hσ]
  · simp

/-! ### `S_k(κ)` is the complement of Lemma 6 -/

/-- `S_k(κ)` is complementary to `κ` in the sense of Lemma 6 (`RMT.Complementary`), so by
`RMT.lemma6` the shifted rows of `κ` and of `S_k(κ)` together list `{0, …, 2k − 1}`. -/
theorem complementary_S (κ : Fin k → ℕ) (hκ : Antitone κ) :
    Complementary k κ (S k κ) := by
  intro j
  set ρ : Fin k → ℕ := fun i => k - κ (Fin.rev i) with hρ
  have hρa : Antitone ρ := fun a b hab => by
    have := hκ (Fin.rev_le_rev.mpr hab)
    simp only [hρ]; omega
  have hiff : ∀ i' : Fin k, (j : ℕ) < tr ρ i' ↔ (i' : ℕ) < ρ j := fun i' =>
    ⟨fun h => by
      by_contra h'
      have := tr_le_of_le hρa (j := j) (c := i') (by omega)
      omega,
     fun h => by
      have := le_tr_of_lt hρa (i := j) (c := i') h
      omega⟩
  have hS : S k κ = fun i' : Fin k => tr ρ i' := rfl
  have hj : ρ j ≤ k := by simp only [hρ]; omega
  rw [tr, hS]
  simp only [hiff]
  rw [Fin.card_filter_val_lt, min_eq_right hj]
  simp only [hρ]
  congr 2
  ext; simp [Fin.val_rev]; omega

theorem complementary_S_lemma6 (κ : Fin k → ℕ) (hκ : Antitone κ) (hb : ∀ i, κ i ≤ k)
    (hSa : Antitone (S k κ)) (hSb : ∀ i, S k κ i ≤ k) : ShiftedPartition k κ (S k κ) :=
  (lemma6 k κ (S k κ) hκ hSa hb hSb).mp (complementary_S κ hκ)

/-! ### Partitions of size 0 and 1, and their complements -/

theorem eq_zero_of_sum_eq_zero {κ : Fin k → ℕ} (h : ∑ i, κ i = 0) : κ = 0 := by
  funext i; exact (sum_eq_zero_iff.mp h) i (mem_univ _)

theorem boxParts_zero (k : ℕ) : boxParts k 0 = {0} := by
  ext κ
  simp only [boxParts, mem_filter, Fintype.mem_piFinset, mem_range, mem_singleton]
  constructor
  · rintro ⟨-, -, hs⟩; exact eq_zero_of_sum_eq_zero hs
  · rintro rfl; simp

/-- An antitone `κ` with `|κ| = 1` is the one-box partition. -/
theorem eq_single_of_sum_eq_one {n : ℕ} {κ : Fin (n + 1) → ℕ}
    (ha : ∀ i j : Fin (n + 1), i ≤ j → κ j ≤ κ i) (hs : ∑ i, κ i = 1) : κ = Pi.single 0 1 := by
  have h0 : ∀ i : Fin (n + 1), i ≠ 0 → κ i = 0 := by
    intro i hi
    have hle := ha 0 i (Fin.zero_le _)
    have : κ 0 + κ i ≤ ∑ j, κ j := by
      rw [← sum_pair (Ne.symm hi)]
      exact sum_le_sum_of_subset (subset_univ _)
    omega
  have h1 : κ 0 = 1 := by
    rw [← add_sum_erase univ κ (mem_univ 0), sum_eq_zero fun i hi => h0 i (ne_of_mem_erase hi)] at hs
    simpa using hs
  funext i
  by_cases hi : i = 0
  · subst hi; simp [h1]
  · simp [hi, h0 i hi]

theorem boxParts_one (n : ℕ) : boxParts (n + 1) 1 = {Pi.single 0 1} := by
  ext κ
  simp only [boxParts, mem_filter, Fintype.mem_piFinset, mem_range, mem_singleton]
  constructor
  · rintro ⟨-, ha, hs⟩; exact eq_single_of_sum_eq_one ha hs
  · rintro rfl
    refine ⟨fun i => ?_, fun i j hij => ?_, by simp⟩
    · by_cases hi : i = 0 <;> simp [hi]
    · by_cases hj : j = 0
      · subst hj; simp [le_antisymm hij (Fin.zero_le _)]
      · simp [hj]

theorem firstRow_zero : FirstRow (0 : Fin k → ℕ) := fun _ _ => rfl

theorem firstRow_single (n : ℕ) : FirstRow (Pi.single 0 1 : Fin (n + 1) → ℕ) := by
  intro i hi
  have : i ≠ 0 := fun h => hi (by simp [h])
  simp [this]

theorem S_zero (k : ℕ) : S k 0 = sq k := by
  funext j; simp [S, tr, sq]

theorem S_single (n : ℕ) : S (n + 1) (Pi.single 0 1) = removeBox (sq (n + 1)) (Fin.last n) := by
  funext j
  simp only [S, tr, removeBox, sq, Function.update_apply]
  have hrev : ∀ i : Fin (n + 1), Fin.rev i = 0 ↔ i = Fin.last n := by
    intro i; rw [Fin.rev_eq_iff, Fin.rev_zero]
  by_cases hj : j = Fin.last n
  · subst hj
    rw [ite_eq_left rfl]
    have : (univ.filter fun i : Fin (n + 1) =>
        ((Fin.last n : Fin (n + 1)) : ℕ) < n + 1 - (Pi.single 0 1 : Fin (n + 1) → ℕ) (Fin.rev i))
        = univ.erase (Fin.last n) := by
      ext i
      by_cases hi : i = Fin.last n
      · subst hi; simp
      · have : Fin.rev i ≠ 0 := fun h => hi ((hrev i).mp h)
        simp [hi, this]
    rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  · rw [ite_eq_right hj]
    have hjn : (j : ℕ) < n := by
      have := j.isLt
      have : (j : ℕ) ≠ n := fun h => hj (Fin.ext (by simpa using h))
      omega
    rw [filter_true_of_mem, card_univ, Fintype.card_fin]
    intro i _
    by_cases hi : Fin.rev i = 0 <;> simp [hi] <;> omega

/-! ### Paths from `∅` and from `□` -/

theorem eq_zero_iff_sum {μ : Fin k → ℕ} : μ = 0 ↔ ∑ i, μ i = 0 :=
  ⟨fun h => by simp [h], eq_zero_of_sum_eq_zero⟩

/-- Paths from `∅` are standard tableaux: `dim(∅, μ) = f^μ`. -/
theorem skewDim_zero_left (f : ℕ) (μ : Fin k → ℕ) : skewDim 0 f μ = fSYT f μ := by
  induction f generalizing μ with
  | zero => simp [skewDim, fSYT, eq_zero_iff_sum]
  | succ f ih => simp [skewDim, fSYT, eq_zero_iff_sum, ih]

theorem corners_single (n : ℕ) :
    univ.filter (fun i => IsCorner (Pi.single 0 1 : Fin (n + 1) → ℕ) i) = {0} := by
  ext i
  rw [mem_filter, mem_singleton]
  simp only [mem_univ, true_and, IsCorner, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hi : i = 0
  · subst hi
    refine iff_of_true ⟨by simp, ?_⟩ rfl
    split
    · next h =>
      have : (⟨(0 : Fin (n + 1)).val + 1, h⟩ : Fin (n + 1)) ≠ 0 := by simp [Fin.ext_iff]
      simp [Fin.ext_iff]
    · rfl
  · simp [hi]

theorem corners_sq (n : ℕ) : univ.filter (fun i => IsCorner (sq (n + 1)) i) = {Fin.last n} := by
  ext i
  rw [mem_filter, mem_singleton]
  simp only [mem_univ, true_and, IsCorner, sq, Bool.and_eq_true]
  by_cases h : (i : ℕ) + 1 < n + 1
  · have : i ≠ Fin.last n := fun e => by subst e; simp at h
    simp [h, this]
  · have : i = Fin.last n := Fin.ext (by simp; omega)
    simp [this]

theorem fSYT_succ_single (n : ℕ) : fSYT 1 (Pi.single 0 1 : Fin (n + 1) → ℕ) = 1 := by
  rw [fSYT, ite_eq_right (by simp), corners_single, sum_singleton]
  have : removeBox (Pi.single 0 1 : Fin (n + 1) → ℕ) 0 = 0 := by
    funext j; by_cases hj : j = 0 <;> simp [removeBox, hj]
  simp [this, fSYT]

/-- Paths from the one-box partition: `dim(□, μ) = f^μ` for `μ ≠ ∅`. -/
theorem skewDim_single (n : ℕ) : ∀ (f : ℕ) (μ : Fin (n + 1) → ℕ), Antitone μ →
    ∑ i, μ i = f + 1 → skewDim (Pi.single 0 1) f μ = fSYT (f + 1) μ := by
  intro f
  induction f with
  | zero =>
    intro μ hμ hs
    obtain rfl : μ = Pi.single 0 1 := eq_single_of_sum_eq_one (fun i j h => hμ h) hs
    simp [skewDim, fSYT_succ_single]
  | succ f ih =>
    intro μ hμ hs
    have hne : μ ≠ Pi.single 0 1 := by
      rintro rfl; simp at hs
    rw [skewDim, ite_eq_right hne, fSYT, ite_eq_right (by omega)]
    have hfilt : (univ.filter fun i => IsCorner μ i ∧
        ∀ j, (Pi.single 0 1 : Fin (n + 1) → ℕ) j ≤ removeBox μ i j) =
        univ.filter fun i => IsCorner μ i := by
      refine filter_congr fun i _ => ⟨fun h => h.1, fun h => ⟨h, fun j => ?_⟩⟩
      obtain ⟨ha, hpos⟩ := removeBox_antitone hμ h
      have hsum := sum_removeBox hpos
      by_cases hj : j = 0
      · subst hj
        simp only [Pi.single_eq_same]
        by_contra h0
        have : ∀ j, removeBox μ i j = 0 := fun j => by
          have := ha (Fin.zero_le j); omega
        simp [this] at hsum; omega
      · simp [hj]
    rw [hfilt]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨ha, hpos⟩ := removeBox_antitone hμ (mem_filter.mp hi).2
    have hsum := sum_removeBox hpos
    exact ih _ ha (by omega)

theorem fSYT_sq (n : ℕ) :
    fSYT ((n + 1) * (n + 1)) (sq (n + 1)) =
      fSYT ((n + 1) * (n + 1) - 1) (removeBox (sq (n + 1)) (Fin.last n)) := by
  obtain ⟨m, hm⟩ : ∃ m, (n + 1) * (n + 1) = m + 1 := ⟨(n + 1) * (n + 1) - 1, by
    have : 0 < (n + 1) * (n + 1) := by positivity
    omega⟩
  rw [hm, fSYT, ite_eq_right (by rw [sum_sq]; omega), corners_sq, sum_singleton, Nat.add_sub_cancel]

/-! ### The exact side: `∏ (i + j − 1)` and `Σ (i + j − 1)` -/

theorem weights_prod (k : ℕ) :
    (weights k).prod = ∏ i : Fin k, ∏ j : Fin k, ((i : ℕ) + (j : ℕ) + 1 : ℚ) := by
  rw [weights, ← Finset.prod_eq_multiset_prod, ← Finset.univ_product_univ, Finset.prod_product]

theorem weights_sum (k : ℕ) :
    (weights k).sum = ∑ i : Fin k, ∑ j : Fin k, ((i : ℕ) + (j : ℕ) + 1 : ℚ) := by
  rw [weights, ← Finset.sum_eq_multiset_sum, ← Finset.univ_product_univ, Finset.sum_product]

/-- Row `i` of the hook product of the square: `i! · ∏_{j<k} (i + j + 1) = (i + k)!`. -/
theorem prod_row (k i : ℕ) : (i ! : ℚ) * ∏ j : Fin k, ((i : ℚ) + (j : ℕ) + 1) = ((i + k)! : ℚ) := by
  rw [Fin.prod_univ_eq_prod_range (fun j => (i : ℚ) + j + 1) k, ← Nat.factorial_mul_ascFactorial,
    Nat.ascFactorial_eq_prod_range]
  push_cast
  congr 1
  exact prod_congr rfl fun j _ => by ring

/-- `∏_{i,j ≤ k} (i + j − 1) = 1/ksConst k`. -/
theorem weights_prod_mul_ksConst (k : ℕ) : (weights k).prod * ksConst k = 1 := by
  rw [weights_prod, ksConst, ← Fin.prod_univ_eq_prod_range, ← prod_mul_distrib]
  refine prod_eq_one fun i _ => ?_
  have h := prod_row k i
  have : (((i : ℕ) + k)! : ℚ) ≠ 0 := by positivity
  field_simp
  linarith

theorem weights_sum_eq (k : ℕ) : (weights k).sum = (k : ℚ) ^ 3 := by
  rw [weights_sum]
  have h : ∑ i : Fin k, ∑ j : Fin k, ((i : ℕ) + (j : ℕ) + 1) = k ^ 3 := by
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
      ← mul_sum, Fin.sum_univ_eq_sum_range (fun i => i) k]
    have h2 := Finset.sum_range_id_mul_two k
    rcases k with _ | n
    · simp
    · simp only [Nat.add_sub_cancel] at h2
      nlinarith [h2]
  exact_mod_cast h

theorem exactCoeff_zero (k : ℕ) : exactCoeff k 0 = ksConst k := by
  have h := weights_prod_mul_ksConst k
  have : (weights k).prod ≠ 0 := left_ne_zero_of_mul_eq_one h
  rw [exactCoeff, Multiset.esymm, Multiset.powersetCard_zero_left]
  simp only [Multiset.map_singleton, Multiset.prod_zero, Multiset.sum_singleton]
  field_simp
  linarith

theorem exactCoeff_one (k : ℕ) : exactCoeff k 1 = (k : ℚ) ^ 3 * ksConst k := by
  have h := weights_prod_mul_ksConst k
  have : (weights k).prod ≠ 0 := left_ne_zero_of_mul_eq_one h
  rw [exactCoeff, Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id', weights_sum_eq]
  rw [show ksConst k = 1 / (weights k).prod from eq_div_of_mul_eq this (by rw [mul_comm]; exact h)]
  ring

/-! ### Theorem 3 for `M = 0` and `M = 1` -/

/-- **Theorem 3, `M = 0`** (the Keating–Snaith constant): `c_0(k) = f^{k×k}/(k²)! = ksConst k`. -/
theorem thm3Coeff_zero (k : ℕ) : thm3Coeff k 0 = ksConst k := by
  simp only [thm3Coeff, thm3CoeffWith, zero_add, range_one, sum_singleton, Nat.sub_zero, boxParts_zero]
  rw [dCoef_firstRow _ firstRow_zero firstRow_zero, fCoef, prodCoef_zero _ (gFun_zero _), S_zero,
    skewDim_zero_left, ← gSYT_eq_fSYT, hookLengthSquare_holds k]
  have : (((k * k)! : ℕ) : ℚ) ≠ 0 := by positivity
  simp only [Pi.zero_apply, sum_const_zero, pow_zero, one_mul]
  field_simp

/-- **Theorem 3, `M = 1`**: `c_1(k) = k · f^{k×k}/(k² − 1)! = k³ · ksConst k`. -/
theorem thm3Coeff_one (n : ℕ) : thm3Coeff (n + 1) 1 = ((n + 1 : ℕ) : ℚ) ^ 3 * ksConst (n + 1) := by
  have hk : 1 ≤ (n + 1) * (n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only [thm3Coeff, thm3CoeffWith, sum_range_succ, range_zero, sum_empty, zero_add, Nat.sub_zero,
    Nat.sub_self, boxParts_zero, boxParts_one, sum_singleton]
  have hg0 := gFun_zero ((n + 1) * (n + 1))
  have hg1 := gFun_one hk
  rw [dCoef_firstRow _ firstRow_zero (firstRow_single n),
    dCoef_firstRow _ (firstRow_single n) firstRow_zero, fCoef,
    prodCoef_single_right _ hg0, prodCoef_single_left _ hg0, countP_cells_fst, countP_cells_snd,
    hg1, S_zero, S_single, skewDim_zero_left,
    skewDim_single n _ _ (fun _ _ _ => le_rfl) (by rw [sum_sq]; omega), Nat.sub_add_cancel hk,
    ← fSYT_sq, ← gSYT_eq_fSYT, hookLengthSquare_holds (n + 1)]
  have hf : (((n + 1) * (n + 1))! : ℚ) = ((n + 1) * (n + 1) : ℕ) * (((n + 1) * (n + 1) - 1)! : ℕ) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred (by positivity)]
  have : ((((n + 1) * (n + 1) - 1)! : ℕ) : ℚ) ≠ 0 := by positivity
  simp only [Pi.zero_apply, sum_const_zero, pow_zero, one_mul, Finset.sum_pi_single', mem_univ,
    ite_true, pow_one]
  rw [hf]
  push_cast
  field_simp
  ring

/-- **Theorem 3 holds for `M = 0`**, for every `k`. -/
theorem theorem3_zero (k : ℕ) : thm3Coeff k 0 = (momentPoly k).coeff (k * k) := by
  rw [← Nat.sub_zero (k * k), momentPoly_coeff k 0 (Nat.zero_le _), thm3Coeff_zero, exactCoeff_zero]

/-- **Theorem 3 holds for `M = 1`**, for every `k ≥ 1`. -/
theorem theorem3_one (k : ℕ) (hk : 1 ≤ k) : thm3Coeff k 1 = (momentPoly k).coeff (k * k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [momentPoly_coeff _ 1 (Nat.one_le_iff_ne_zero.mpr (by positivity)), thm3Coeff_one,
    exactCoeff_one]

end RMT.UN
