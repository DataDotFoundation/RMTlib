import RMTlib.Tableaux.Exclusion

/-!
# Frobenius's hook identity

For a partition `ν` with at most `N` parts, with shifted parts `ℓ_i = ν_i + N − 1 − i`,

  `H(ν) · ∏_{i<j} (ℓ_i − ℓ_j) = ∏_i ℓ_i!`,

where `H(ν)` is the product of the hook lengths. The proof goes row by row: the hook lengths in
row `i` and the gaps `ℓ_i − ℓ_j` (`j > i`) list `{1, …, ℓ_i}` exactly once (`row_partition`),
by the same case split as Macdonald's identity (`RMT.macdonald_1_7`).

The RH formalisation proves `‖hw_ν‖²_Fock · ∏_{i<j} (ℓ_i − ℓ_j) = ∏_i ℓ_i!`
(`PI.HookSteps.HookNorm`). Together with `frobenius`, the bridge package concludes that the Fock
norm² of every highest-weight vector is the hook product `H(ν)`
(`RMT.Bridge.fockQ_hw_eq_hookProd`), not just for the square.
-/

open Finset
open scoped Nat

namespace RMT

variable {N : ℕ}

/-- The shifted part `ℓ_i = ν_i + N − 1 − i`. -/
def ell (ν : Fin N → ℕ) (i : Fin N) : ℕ := ν i + (N - 1 - i)

/-- The hook length of the box `(i, c)` (`c < ν_i`): arm `ν_i − c − 1`, leg `ν'_c − i − 1`, plus one. -/
def hook (ν : Fin N → ℕ) (i : Fin N) (c : ℕ) : ℕ := ν i - c + tr ν c - i - 1

/-- The hook product `H(ν)`. -/
def hookProd (ν : Fin N → ℕ) : ℕ := ∏ i, ∏ c ∈ range (ν i), hook ν i c

/-- Rows up to `i` are longer than `c` when the box `(i, c)` is in `ν`. -/
theorem le_tr_of_lt {ν : Fin N → ℕ} (hν : Antitone ν) {i : Fin N} {c : ℕ} (h : c < ν i) :
    i.val + 1 ≤ tr ν c := by
  unfold tr
  calc i.val + 1 = #(Iic i) := by rw [Fin.card_Iic]
    _ ≤ _ := card_le_card (by
        intro i' hi'
        simp only [mem_filter, mem_univ, true_and]
        exact lt_of_lt_of_le h (hν (mem_Iic.mp hi')))

/-- Only rows before `j` can be longer than `c` when the box `(j, c)` is not in `ν`. -/
theorem tr_le_of_le {ν : Fin N → ℕ} (hν : Antitone ν) {j : Fin N} {c : ℕ} (h : ν j ≤ c) :
    tr ν c ≤ j.val := by
  unfold tr
  calc #({i' : Fin N | c < ν i'}) ≤ #(Iio j) := card_le_card (by
        intro i' hi'
        simp only [mem_filter, mem_univ, true_and] at hi'
        rw [mem_Iio]
        by_contra hge
        exact absurd (lt_of_lt_of_le hi' (hν (not_lt.mp hge))) (by omega))
    _ = j.val := by rw [Fin.card_Iio]

theorem tr_le' (ν : Fin N → ℕ) (c : ℕ) : tr ν c ≤ N := tr_le ν c

/-- The hook lengths of row `i` and the gaps `ℓ_i − ℓ_j`, `j > i`, list `{1, …, ℓ_i}` once. -/
theorem row_partition (ν : Fin N → ℕ) (hν : Antitone ν) (i : Fin N) :
    Disjoint ((range (ν i)).image (hook ν i)) ((Ioi i).image fun j => ell ν i - ell ν j) ∧
      (range (ν i)).image (hook ν i) ∪ (Ioi i).image (fun j => ell ν i - ell ν j) = Ico 1 (ell ν i + 1) := by
  have hiN := i.isLt
  -- hooks are strictly decreasing along the row
  have hook_inj : Set.InjOn (hook ν i) (range (ν i) : Set ℕ) := by
    intro c hc c' hc' h
    simp only [coe_range, Set.mem_Iio] at hc hc'
    have h1 := le_tr_of_lt hν hc
    have h1' := le_tr_of_lt hν hc'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := tr_antitone ν (j := c) (j' := c') hlt.le
      simp only [hook] at h; omega
    · have := tr_antitone ν (j := c') (j' := c) hlt.le
      simp only [hook] at h; omega
  have gap_inj : Set.InjOn (fun j : Fin N => ell ν i - ell ν j) (Ioi i : Set (Fin N)) := by
    intro j hj j' hj' h
    simp only [coe_Ioi, Set.mem_Ioi] at hj hj'
    have hji : (i : ℕ) < j := hj
    have hji' : (i : ℕ) < j' := hj'
    have a1 := hν hj.le; have a2 := hν hj'.le
    simp only [ell] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hν hlt.le; have : (j : ℕ) < j' := hlt; have := j'.isLt; omega
    · have := hν hlt.le; have : (j' : ℕ) < j := hlt; have := j.isLt; omega
  have hdisj : Disjoint ((range (ν i)).image (hook ν i)) ((Ioi i).image fun j => ell ν i - ell ν j) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
    obtain ⟨j, hj, hj'⟩ := mem_image.mp hx'
    rw [mem_range] at hc
    rw [mem_Ioi] at hj
    have hji : (i : ℕ) < j := hj
    have hjN := j.isLt
    have hνj := hν hj.le
    have h1 := le_tr_of_lt hν hc
    simp only [ell, hook] at hj'
    by_cases hb : c < ν j
    · have := le_tr_of_lt hν hb
      have := tr_le ν c
      omega
    · have := tr_le_of_le hν (not_lt.mp hb)
      omega
  refine ⟨hdisj, ?_⟩
  have hsub : (range (ν i)).image (hook ν i) ∪ (Ioi i).image (fun j => ell ν i - ell ν j) ⊆
      Ico 1 (ell ν i + 1) := by
    intro x hx
    rw [mem_Ico]
    rcases mem_union.mp hx with h | h
    · obtain ⟨c, hc, rfl⟩ := mem_image.mp h
      rw [mem_range] at hc
      have := le_tr_of_lt hν hc
      have := tr_le ν c
      simp only [hook, ell]
      omega
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp h
      rw [mem_Ioi] at hj
      have hji : (i : ℕ) < j := hj
      have := hν hj.le
      have := j.isLt
      simp only [ell]
      omega
  refine eq_of_subset_of_card_le hsub ?_
  rw [card_union_of_disjoint hdisj, card_image_of_injOn hook_inj, card_image_of_injOn gap_inj,
    card_range, Nat.card_Ico, Fin.card_Ioi]
  simp only [ell]
  omega

/-- One row: `∏_c hook(i, c) · ∏_{j>i} (ℓ_i − ℓ_j) = ℓ_i!`. -/
theorem row_identity (ν : Fin N → ℕ) (hν : Antitone ν) (i : Fin N) :
    (∏ c ∈ range (ν i), hook ν i c) * (∏ j ∈ Ioi i, (ell ν i - ell ν j)) = (ell ν i)! := by
  obtain ⟨hd, hu⟩ := row_partition ν hν i
  have hiN := i.isLt
  have hook_inj : Set.InjOn (hook ν i) (range (ν i) : Set ℕ) := by
    intro c hc c' hc' h
    simp only [coe_range, Set.mem_Iio] at hc hc'
    have h1 := le_tr_of_lt hν hc
    have h1' := le_tr_of_lt hν hc'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := tr_antitone ν (j := c) (j' := c') hlt.le
      simp only [hook] at h; omega
    · have := tr_antitone ν (j := c') (j' := c) hlt.le
      simp only [hook] at h; omega
  have gap_inj : Set.InjOn (fun j : Fin N => ell ν i - ell ν j) (Ioi i : Set (Fin N)) := by
    intro j hj j' hj' h
    simp only [coe_Ioi, Set.mem_Ioi] at hj hj'
    have a1 := hν hj.le; have a2 := hν hj'.le
    have hji : (i : ℕ) < j := hj
    have hji' : (i : ℕ) < j' := hj'
    simp only [ell] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hν hlt.le; have : (j : ℕ) < j' := hlt; have := j'.isLt; omega
    · have := hν hlt.le; have : (j' : ℕ) < j := hlt; have := j.isLt; omega
  have e1 : ∏ c ∈ range (ν i), hook ν i c = ∏ x ∈ (range (ν i)).image (hook ν i), x :=
    (prod_image (f := fun x => x) hook_inj).symm
  have e2 : ∏ j ∈ Ioi i, (ell ν i - ell ν j) = ∏ x ∈ (Ioi i).image (fun j => ell ν i - ell ν j), x :=
    (prod_image (f := fun x => x) gap_inj).symm
  rw [e1, e2, ← prod_union hd, hu, prod_Ico_id_eq_factorial]

/-- **Frobenius's hook identity.** -/
theorem frobenius (ν : Fin N → ℕ) (hν : Antitone ν) :
    hookProd ν * ∏ i, ∏ j ∈ Ioi i, (ν i - ν j + (j - i)) = ∏ i, (ν i + (N - 1 - i))! := by
  have hgap : ∀ i j : Fin N, j ∈ Ioi i → ν i - ν j + (j - i) = ell ν i - ell ν j := by
    intro i j hj
    rw [mem_Ioi] at hj
    have : (i : ℕ) < j := hj
    have := hν hj.le
    have := j.isLt
    simp only [ell]
    omega
  rw [hookProd, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [prod_congr rfl (hgap i), row_identity ν hν i]
  rfl

/-! ### Bounds on the hook product

`∏ ν_i! ≤ H(ν) ≤ ∏ ν_i! · (ν₀ + N)^{N(N−1)/2}`. Through `‖hw_ν‖²_Fock = H(ν)` these are the
RH formalisation's `PI.HookBound` (proved there through the Capelli identity), which feeds its
lower slope inequality for the families of the zero-free argument. -/

theorem le_hook {ν : Fin N → ℕ} (hν : Antitone ν) {i : Fin N} {c : ℕ} (hc : c < ν i) :
    ν i - c ≤ hook ν i c := by
  have := le_tr_of_lt hν hc
  simp only [hook]
  omega

/-- `∏ ν_i! ≤ H(ν)`: each hook is at least its arm plus one. -/
theorem prod_factorial_le_hookProd (ν : Fin N → ℕ) (hν : Antitone ν) :
    ∏ i, (ν i)! ≤ hookProd ν := by
  refine prod_le_prod fun i _ => ?_
  calc (ν i)! = ∏ c ∈ range (ν i), (ν i - c) := by
        rw [← prod_range_add_one_eq_factorial, ← prod_range_reflect]
        refine prod_congr rfl fun c hc => ?_
        have := mem_range.mp hc
        omega
    _ ≤ ∏ c ∈ range (ν i), hook ν i c :=
        prod_le_prod fun c hc => le_hook hν (mem_range.mp hc)

theorem factorial_add_le (a m : ℕ) : (a + m)! ≤ a ! * (a + m) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc (a + (m + 1))! = (a + m + 1) * (a + m)! := by rw [← add_assoc, Nat.factorial_succ]
      _ ≤ (a + m + 1) * (a ! * (a + m) ^ m) := Nat.mul_le_mul_left _ ih
      _ ≤ (a + (m + 1)) * (a ! * (a + (m + 1)) ^ m) := by
          rw [← add_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      _ = a ! * (a + (m + 1)) ^ (m + 1) := by ring

theorem sum_fin_sub_one_sub (N : ℕ) : ∑ i : Fin N, (N - 1 - i) = N * (N - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, ← Finset.sum_range_reflect (fun i => N - 1 - i) N]
  have : ∑ j ∈ range N, (N - 1 - (N - 1 - j)) = ∑ j ∈ range N, j :=
    sum_congr rfl fun j hj => by have := mem_range.mp hj; omega
  rw [this, Finset.sum_range_id]

/-- `H(ν) ≤ ∏ ν_i! · (ν₀ + N)^{N(N−1)/2}`, from Frobenius's identity. -/
theorem hookProd_le (ν : Fin N → ℕ) (hν : Antitone ν) (hN : 0 < N) :
    hookProd ν ≤ (∏ i, (ν i)!) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by
  have hF := frobenius ν hν
  have hP : 1 ≤ ∏ i, ∏ j ∈ Ioi i, (ν i - ν j + (j - i)) := by
    refine Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j hj => ?_)
    rw [mem_Ioi] at hj
    have : (i : ℕ) < j := hj
    omega
  have h1 : hookProd ν ≤ ∏ i, (ν i + (N - 1 - i))! := by
    calc hookProd ν = hookProd ν * 1 := (mul_one _).symm
      _ ≤ hookProd ν * ∏ i, ∏ j ∈ Ioi i, (ν i - ν j + (j - i)) := Nat.mul_le_mul_left _ hP
      _ = _ := hF
  refine h1.trans ?_
  rw [← sum_fin_sub_one_sub, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_le_prod fun i _ => ?_
  calc (ν i + (N - 1 - i))! ≤ (ν i)! * (ν i + (N - 1 - i)) ^ (N - 1 - i) := factorial_add_le _ _
    _ ≤ (ν i)! * (ν ⟨0, hN⟩ + N) ^ (N - 1 - i) := by
        refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
        have := hν (show (⟨0, hN⟩ : Fin N) ≤ i from by rw [Fin.le_def]; exact Nat.zero_le _)
        omega

end RMT
