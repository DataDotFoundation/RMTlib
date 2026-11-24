import RMTlib.Tableaux.JacobiTrudi

open Finset Polynomial
open scoped Nat

namespace RMT

/-- **Upward Lagrange identity**: for distinct `x_i`, `Σ_i ∏_{j≠i} (x_i − x_j + 1)/(x_i − x_j) = N`. -/
theorem lagrange_up (N : ℕ) (x : Fin N → ℚ) (hx : Function.Injective x) :
    ∑ i, ∏ j ∈ univ.erase i, (x i - x j + 1) / (x i - x j) = N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set P := Lagrange.nodal univ x with hP
  set Q := Lagrange.nodal univ (fun j => x j - 1) with hQ
  have hPd : P.natDegree = N := by rw [hP, Lagrange.natDegree_nodal, card_univ, Fintype.card_fin]
  have hQd : Q.natDegree = N := by rw [hQ, Lagrange.natDegree_nodal, card_univ, Fintype.card_fin]
  have hdeg : (Q - P).degree < #(univ : Finset (Fin N)) := by
    rw [card_univ, Fintype.card_fin]
    have := degree_sub_lt_left (p := Q) (q := P)
      (by rw [degree_eq_natDegree (Lagrange.nodal_monic).ne_zero,
        degree_eq_natDegree (Lagrange.nodal_monic).ne_zero, hPd, hQd])
      (Lagrange.nodal_monic).ne_zero
      (by rw [(Lagrange.nodal_monic).leadingCoeff, (Lagrange.nodal_monic).leadingCoeff])
    rwa [degree_eq_natDegree (Lagrange.nodal_monic).ne_zero, hQd] at this
  have hs := Lagrange.coeff_eq_sum (s := univ) (v := x) hx.injOn hdeg
  rw [card_univ, Fintype.card_fin] at hs
  have hcoeff : (Q - P).coeff (N - 1) = N := by
    rw [coeff_sub, ← hQd, ← nextCoeff_of_natDegree_pos (by omega), hQd, ← hPd,
      ← nextCoeff_of_natDegree_pos (by omega), hQ, hP, Lagrange.nodal, Lagrange.nodal,
      prod_X_sub_C_nextCoeff, prod_X_sub_C_nextCoeff, sum_sub_distrib]
    simp
  rw [hcoeff] at hs
  rw [hs]
  refine sum_congr rfl fun i _ => ?_
  rw [prod_div_distrib]
  congr 1
  symm
  rw [eval_sub, hP, Lagrange.eval_nodal_at_node (mem_univ i), sub_zero, hQ,
    Lagrange.eval_nodal, ← mul_prod_erase univ _ (mem_univ i)]
  simp only [sub_sub_cancel, one_mul]
  exact prod_congr rfl fun j _ => by ring

variable {N : ℕ}

/-- Raising `x_k` by one multiplies the Vandermonde product by
`∏_{j≠k} (x_k − x_j + 1)/(x_k − x_j)`. -/
theorem vand_update_add (x : Fin N → ℚ) (hx : Function.Injective x) (k : Fin N) :
    vand (Function.update x k (x k + 1)) =
      vand x * ∏ j ∈ univ.erase k, (x k - x j + 1) / (x k - x j) := by
  have hne : ∀ i j, i ≠ j → x i - x j ≠ 0 := fun i j h => sub_ne_zero.mpr (hx.ne h)
  have hV : vand x ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j hj =>
      hne i j (ne_of_lt (mem_Ioi.mp hj))
  set x' := Function.update x k (x k + 1) with hx'
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

/-- Add a box at the end of row `i`. -/
def addBox (ν : Fin N → ℕ) (i : Fin N) : Fin N → ℕ := Function.update ν i (ν i + 1)

/-- A box can be added to row `i`: `i = 0` or the row above is longer. -/
def IsAddable (ν : Fin N → ℕ) (i : Fin N) : Bool :=
  if h : 0 < i.val then ν i < ν ⟨i.val - 1, by omega⟩ else true

theorem ellQ_addBox (ν : Fin N → ℕ) (k : Fin N) :
    ellQ (addBox ν k) = Function.update (ellQ ν) k (ellQ ν k + 1) := by
  funext i
  by_cases h : i = k
  · subst h
    simp only [ellQ, ell, addBox, Function.update_self]
    push_cast
    ring
  · simp only [ellQ, ell, addBox, Function.update_of_ne h]

/-- Weyl's dimension formula, Vandermonde form. -/
theorem gtCount_eq_vand (ν : Fin N → ℕ) (hν : Antitone ν) :
    (gtCount N ν : ℚ) = vand (ellQ ν) / vand (ellQ (0 : Fin N → ℕ)) := by
  obtain ⟨c, hc, hB⟩ := binDet_eq_mul_vand (n := N)
  rw [gtCount_eq_binDet N ν hν, hB, hB, mul_div_mul_left _ _ hc]
  rfl

theorem addBox_antitone {ν : Fin N → ℕ} (hν : Antitone ν) {k : Fin N}
    (hk : IsAddable ν k = true) : Antitone (addBox ν k) := by
  intro a b hab
  simp only [addBox, Function.update_apply]
  have := hν hab
  split_ifs with hb ha ha
  · omega
  · have hab' : (a : ℕ) < k := Fin.lt_def.mp (lt_of_le_of_ne (hb ▸ hab) ha)
    have hpos : 0 < (k : ℕ) := by omega
    simp only [IsAddable, dif_pos hpos, decide_eq_true_eq] at hk
    have := hν (show a ≤ ⟨k.val - 1, by omega⟩ from Fin.le_def.mpr (by simp; omega))
    omega
  · rw [ha] at this; omega
  · exact this

/-- **Pieri's rule at `1^N`**: `N · #GT(μ) = Σ_{μ + □} #GT(μ + □)`. -/
theorem pieri_gtCount (μ : Fin N → ℕ) (hμ : Antitone μ) :
    (N : ℚ) * gtCount N μ =
      ∑ i ∈ univ.filter (fun i => IsAddable μ i), (gtCount N (addBox μ i) : ℚ) := by
  have hinj := ellQ_injective hμ
  set T : Fin N → ℚ := fun i =>
    ∏ j ∈ univ.erase i, (ellQ μ i - ellQ μ j + 1) / (ellQ μ i - ellQ μ j) with hT
  have hterm : ∀ i, IsAddable μ i = true →
      (gtCount N (addBox μ i) : ℚ) = gtCount N μ * T i := by
    intro i hi
    rw [gtCount_eq_vand _ (addBox_antitone hμ hi), gtCount_eq_vand _ hμ, ellQ_addBox,
      vand_update_add _ hinj]
    ring
  have hzero : ∀ i, IsAddable μ i = false → T i = 0 := by
    intro i hi
    have hpos : 0 < (i : ℕ) := by
      by_contra h0
      simp [IsAddable, h0] at hi
    simp only [IsAddable, dif_pos hpos, decide_eq_false_iff_not, not_lt] at hi
    have hle := hμ (show (⟨i.val - 1, by omega⟩ : Fin N) ≤ i from Fin.le_def.mpr (by simp))
    refine prod_eq_zero (i := ⟨i.val - 1, by omega⟩)
      (mem_erase.mpr ⟨by simp [Fin.ext_iff]; omega, mem_univ _⟩) ?_
    have : ell μ ⟨i.val - 1, by omega⟩ = ell μ i + 1 := by
      simp only [ell]; have := i.isLt; omega
    simp only [ellQ, this]
    push_cast
    ring
  rw [sum_congr rfl fun i hi => hterm i (mem_filter.mp hi).2,
    sum_filter_of_ne fun i _ h => by
      by_contra hc
      exact h (by rw [hzero i (by simpa using hc)]; ring),
    ← mul_sum, hT, lagrange_up N _ hinj]
  ring

/-! ### Double counting over partitions -/

open Classical in
/-- Partitions of `m` with at most `N` parts. -/
noncomputable def parts (N m : ℕ) : Finset (Fin N → ℕ) :=
  (Fintype.piFinset fun _ : Fin N => range (m + 1)).filter fun ν => Antitone ν ∧ ∑ i, ν i = m

theorem mem_parts {m : ℕ} {ν : Fin N → ℕ} : ν ∈ parts N m ↔ Antitone ν ∧ ∑ i, ν i = m := by
  simp only [parts, mem_filter, Fintype.mem_piFinset, mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h1, h2⟩
    have := single_le_sum (fun j _ => Nat.zero_le (ν j)) (mem_univ i)
    omega

theorem sum_addBox (ν : Fin N → ℕ) (k : Fin N) : ∑ i, addBox ν k i = ∑ i, ν i + 1 := by
  rw [← add_sum_erase univ _ (mem_univ k), ← add_sum_erase univ ν (mem_univ k)]
  have : ∑ i ∈ univ.erase k, addBox ν k i = ∑ i ∈ univ.erase k, ν i :=
    sum_congr rfl fun i hi => Function.update_of_ne (ne_of_mem_erase hi) _ _
  rw [this, addBox, Function.update_self]
  ring

theorem addBox_removeBox {ν : Fin N → ℕ} {k : Fin N} (hk : 0 < ν k) :
    addBox (removeBox ν k) k = ν := by
  funext i
  by_cases h : i = k
  · subst h; simp [addBox, removeBox]; omega
  · simp [addBox, removeBox, Function.update_of_ne h]

theorem removeBox_addBox (ν : Fin N → ℕ) (k : Fin N) : removeBox (addBox ν k) k = ν := by
  funext i
  by_cases h : i = k
  · subst h; simp [addBox, removeBox]
  · simp [addBox, removeBox, Function.update_of_ne h]

theorem isAddable_removeBox {ν : Fin N → ℕ} (hν : Antitone ν) {k : Fin N} (hk : 0 < ν k) :
    IsAddable (removeBox ν k) k = true := by
  unfold IsAddable
  split_ifs with hpos
  · have hne : (⟨k.val - 1, by omega⟩ : Fin N) ≠ k := by simp [Fin.ext_iff]; omega
    have := hν (show (⟨k.val - 1, by omega⟩ : Fin N) ≤ k from Fin.le_def.mpr (by simp))
    simp only [removeBox, Function.update_self, Function.update_of_ne hne, decide_eq_true_eq]
    omega
  · rfl

theorem isCorner_addBox {ν : Fin N → ℕ} (hν : Antitone ν) (k : Fin N) :
    IsCorner (addBox ν k) k = true := by
  simp only [IsCorner, addBox, Function.update_self, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, ?_⟩
  split_ifs with h
  · have hne : (⟨k.val + 1, h⟩ : Fin N) ≠ k := by simp [Fin.ext_iff]
    have := hν (show k ≤ ⟨k.val + 1, h⟩ from Fin.le_def.mpr (by simp))
    simp only [Function.update_of_ne hne, decide_eq_true_eq]
    omega
  · rfl

/-- **Double counting**: removing a corner from a partition of `m + 1` and adding a box to a
partition of `m` are inverse. -/
theorem sum_parts_succ (g : (Fin N → ℕ) → ℚ) (m : ℕ) :
    ∑ ν ∈ parts N (m + 1), (fSYT (m + 1) ν : ℚ) * g ν =
      ∑ μ ∈ parts N m, (fSYT m μ : ℚ) * ∑ i ∈ univ.filter (fun i => IsAddable μ i), g (addBox μ i) := by
  have hL : ∀ ν ∈ parts N (m + 1), (fSYT (m + 1) ν : ℚ) * g ν =
      ∑ i ∈ univ.filter (fun i => IsCorner ν i), (fSYT m (removeBox ν i) : ℚ) * g ν := by
    intro ν hν
    rw [mem_parts] at hν
    rw [fSYT, if_neg (by omega), Nat.cast_sum, sum_mul]
  rw [sum_congr rfl hL, sum_congr rfl fun μ _ => mul_sum _ _ _, sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨removeBox x.1 x.2, x.2⟩) (fun y _ => ⟨addBox y.1 y.2, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨ν, i⟩ hx
    simp only [mem_sigma, mem_filter, mem_univ, true_and, mem_parts] at hx ⊢
    obtain ⟨⟨hν, hs⟩, hc⟩ := hx
    obtain ⟨ha, hpos⟩ := removeBox_antitone hν hc
    have := sum_removeBox hpos
    exact ⟨⟨ha, by omega⟩, isAddable_removeBox hν hpos⟩
  · rintro ⟨μ, i⟩ hy
    simp only [mem_sigma, mem_filter, mem_univ, true_and, mem_parts] at hy ⊢
    obtain ⟨⟨hμ, hs⟩, ha⟩ := hy
    exact ⟨⟨addBox_antitone hμ ha, by rw [sum_addBox, hs]⟩, isCorner_addBox hμ i⟩
  · rintro ⟨ν, i⟩ hx
    simp only [mem_sigma, mem_filter, mem_univ, true_and, mem_parts] at hx
    obtain ⟨_, hpos⟩ := removeBox_antitone hx.1.1 hx.2
    simp [addBox_removeBox hpos]
  · rintro ⟨μ, i⟩ _
    simp [removeBox_addBox]
  · rintro ⟨ν, i⟩ hx
    simp only [mem_sigma, mem_filter, mem_univ, true_and, mem_parts] at hx
    obtain ⟨_, hpos⟩ := removeBox_antitone hx.1.1 hx.2
    simp only [addBox_removeBox hpos]

theorem gtCount_zero : ∀ n : ℕ, gtCount n (0 : Fin n → ℕ) = 1
  | 0 => rfl
  | n + 1 => by
    rw [gtCount]
    have : Fintype.piFinset (fun i : Fin n =>
        Icc ((0 : Fin (n + 1) → ℕ) i.succ) ((0 : Fin (n + 1) → ℕ) i.castSucc)) = {0} := by
      ext μ
      simp only [Fintype.mem_piFinset, Pi.zero_apply, Icc_self, mem_singleton]
      exact ⟨fun h => funext h, fun h i => congrFun h i⟩
    rw [this, sum_singleton, gtCount_zero n]

theorem parts_zero : parts N 0 = {0} := by
  ext ν
  rw [mem_parts, mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    funext i
    exact (sum_eq_zero_iff.mp h) i (mem_univ _)
  · rintro rfl
    exact ⟨fun _ _ _ => le_rfl, by simp⟩

/-- **`Σ_{λ ⊢ m} f^λ · s_λ(1^N) = N^m`**: words of length `m` in `N` letters, counted by the
branching (`fSYT`) and Pieri (`gtCount`) recursions. -/
theorem sum_fSYT_mul_gtCount (m : ℕ) :
    ∑ ν ∈ parts N m, (fSYT m ν : ℚ) * gtCount N ν = (N : ℚ) ^ m := by
  induction m with
  | zero => simp [parts_zero, fSYT, gtCount_zero]
  | succ m ih =>
    rw [sum_parts_succ (fun ν => (gtCount N ν : ℚ)), pow_succ, ← ih, sum_mul]
    refine sum_congr rfl fun μ hμ => ?_
    rw [← pieri_gtCount μ (mem_parts.mp hμ).1]
    ring

end RMT
