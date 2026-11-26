import RMTlib.Tableaux.MultisetHook.Maya

/-!
# `φ_t` is a bijection, and Theorem 1

The last part of Dehaye–Han's Theorem 1: `λ ↦ v(λ)` is a bijection from `t`-cores onto
`V_t`-codings.

* **Injectivity** (`eq_of_vCoding_eq`): the coding gives `V`, `V` gives the Maya diagram of a
  `t`-core (`occ_iff_vSet`), and the Maya diagram gives `λ` (`eq_of_occ`: a strictly decreasing
  sequence is determined by its set of values).
* **Surjectivity** (`exists_of_isVCoding`): every Maya diagram is a shifted partition
  (`exists_of_maya`: the fermionic half of the boson–fermion correspondence, on sets). A coding
  `k` defines the `t`-stable diagram `M = ⋃_i (k_i − tℕ)`, hence a `t`-core `λ` with
  `v(λ) = v − c` for some shift `c`. Both codings sum to zero, the second by the charge
  identity (N6), so `t·c = 0` and `c = 0`. The charge is never counted directly.

`theorem1 : Theorem1` is then `statement_of_bijective`.
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

open Classical

/-! ### Strictly decreasing sequences -/

/-- A strictly decreasing integer sequence on `Fin n` drops by at least one per step. -/
theorem StrictAnti.add_le {n : ℕ} {f : Fin n → ℤ} (hf : StrictAnti f) {i j : Fin n}
    (h : i ≤ j) : f j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ f i := by
  suffices key : ∀ d : ℕ, ∀ i j : Fin n, (j : ℕ) = i + d → f j + d ≤ f i by
    have := key ((j : ℕ) - i) i j (by have := Fin.le_iff_val_le_val.mp h; omega)
    rwa [Nat.cast_sub (Fin.le_iff_val_le_val.mp h)] at this
  intro d
  induction d with
  | zero => intro i j hij; have : i = j := Fin.ext (by omega); subst this; simp
  | succ d ih =>
    intro i j hij
    have hj' : (i : ℕ) + d < n := by omega
    have h1 := ih i ⟨i + d, hj'⟩ rfl
    have h2 : f j < f ⟨i + d, hj'⟩ := hf (Fin.lt_def.mpr (by simp; omega))
    push_cast; linarith

/-- Two strictly decreasing sequences `ℕ → ℤ` with the same values are equal. -/
theorem eq_of_strictAnti_range {f g : ℕ → ℤ} (hf : StrictAnti f) (hg : StrictAnti g)
    (h : ∀ x, (∃ i, f i = x) ↔ (∃ i, g i = x)) : f = g := by
  funext i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    obtain ⟨j, hj⟩ := (h (f i)).mp ⟨i, rfl⟩
    obtain ⟨j', hj'⟩ := (h (g i)).mpr ⟨i, rfl⟩
    have hji : i ≤ j := by
      by_contra hlt
      have := ih j (by omega)
      exact absurd (hf.injective (this.trans hj)) (by omega)
    have hji' : i ≤ j' := by
      by_contra hlt
      have := ih j' (by omega)
      exact absurd (hg.injective (this.symm.trans hj')) (by omega)
    have a := hg.antitone hji
    have b := hf.antitone hji'
    rw [hj] at a; rw [hj'] at b
    exact le_antisymm a b

/-- **A Young diagram is determined by its Maya diagram.** -/
theorem eq_of_occ {μ μ' : YoungDiagram} (h : ∀ x, Occ μ x ↔ Occ μ' x) : μ = μ' := by
  have hs := eq_of_strictAnti_range (site_strictAnti μ) (site_strictAnti μ') fun x => h x
  have hr : ∀ i, μ.rowLen i = μ'.rowLen i := fun i => by
    have := congrFun hs i; unfold site at this; omega
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen, hr]

/-! ### Every Maya diagram is a shifted partition -/

/-- The Young diagram with row lengths `w`, for `w` antitone and zero from `N` on. -/
def ofRows (w : ℕ → ℕ) (hw : Antitone w) (N : ℕ) : YoungDiagram where
  cells := ((range N) ×ˢ (range (w 0))).filter fun c => c.2 < w c.1
  isLowerSet := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨hi : i' ≤ i, hj : j' ≤ j⟩ hc
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hc ⊢
    have := hw hi; have := hw (Nat.zero_le i')
    exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem mem_ofRows {w : ℕ → ℕ} {hw : Antitone w} {N : ℕ} (hN : ∀ i, N ≤ i → w i = 0)
    {i j : ℕ} : (i, j) ∈ ofRows w hw N ↔ j < w i := by
  rw [← YoungDiagram.mem_cells]
  simp only [ofRows, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    have := hw (Nat.zero_le i)
    refine ⟨⟨?_, by omega⟩, h⟩
    by_contra hi; rw [hN i (by omega)] at h; omega

theorem rowLen_ofRows {w : ℕ → ℕ} {hw : Antitone w} {N : ℕ} (hN : ∀ i, N ≤ i → w i = 0)
    (i : ℕ) : (ofRows w hw N).rowLen i = w i := by
  have key : ∀ j, j < (ofRows w hw N).rowLen i ↔ j < w i := fun j => by
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_ofRows hN]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact lt_irrefl _ ((key _).mpr h)
  · exact lt_irrefl _ ((key _).mp h)

/-- **Every Maya diagram is a shifted partition**: a set `M ⊆ ℤ` containing everything below `L`
and nothing above `U` is `M(λ) + c` for a Young diagram `λ` and a charge `c`. -/
theorem exists_of_maya (M : ℤ → Prop) (L U : ℤ) (hL : ∀ x < L, M x) (hU : ∀ x, M x → x ≤ U) :
    ∃ μ : YoungDiagram, ∃ c : ℤ, ∀ x, Occ μ x ↔ M (x + c) := by
  set S := (Icc L U).filter M
  set n := S.card
  set e := S.orderEmbOfFin rfl
  let p : Fin n → ℤ := fun i => e i.rev
  have hp : StrictAnti p := fun i j hij => e.strictMono (Fin.rev_lt_rev.mpr hij)
  have hpS : ∀ i, p i ∈ S := fun i => orderEmbOfFin_mem _ _ _
  have hpL : ∀ i, L ≤ p i := fun i => (mem_Icc.mp (mem_filter.mp (hpS i)).1).1
  set c : ℤ := n + L
  -- the shifted rows `p_i − c + i + 1` are nonnegative and nonincreasing
  have hrow : ∀ i : Fin n, 0 ≤ p i - c + i + 1 := fun i => by
    have hlast : (i : ℕ) ≤ n - 1 := by omega
    have := StrictAnti.add_le hp (j := ⟨n - 1, by omega⟩) (Fin.le_iff_val_le_val.mpr hlast)
    have := hpL ⟨n - 1, by omega⟩
    simp only [c]; push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at *; linarith
  let w : ℕ → ℕ := fun i => if h : i < n then (p ⟨i, h⟩ - c + i + 1).toNat else 0
  have hw : Antitone w := by
    intro i j hij
    simp only [w]
    by_cases hj : j < n
    · rw [dite_eq_left hj, dite_eq_left (by omega)]
      have := StrictAnti.add_le hp (i := ⟨i, by omega⟩) (j := ⟨j, hj⟩) (Fin.le_iff_val_le_val.mpr hij)
      simp only at this
      have h1 := hrow ⟨j, hj⟩
      omega
    · rw [dite_eq_right hj]; exact Nat.zero_le _
  have hN : ∀ i, n ≤ i → w i = 0 := fun i hi => by simp only [w]; rw [dite_eq_right (by omega)]
  refine ⟨ofRows w hw n, c, fun x => ?_⟩
  have hsite : ∀ i, site (ofRows w hw n) i = if h : i < n then p ⟨i, h⟩ - c else -i - 1 := by
    intro i
    unfold site
    rw [rowLen_ofRows hN]
    simp only [w]
    split_ifs with h
    · have := hrow ⟨i, h⟩; simp only at this; omega
    · simp
  constructor
  · rintro ⟨i, rfl⟩
    rw [hsite]
    split_ifs with h
    · rw [sub_add_cancel]; exact (mem_filter.mp (hpS _)).2
    · apply hL; simp only [c]; omega
  · intro hx
    by_cases hxL : L ≤ x + c
    · have hS : x + c ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨hxL, hU _ hx⟩, hx⟩
      have : x + c ∈ Set.range e := by rw [range_orderEmbOfFin]; exact hS
      obtain ⟨j, hj⟩ := this
      refine ⟨j.rev, ?_⟩
      rw [hsite, dite_eq_left j.rev.isLt]
      simp only [p, Fin.eta, Fin.rev_rev, hj]; ring
    · refine ⟨(-x - 1).toNat, ?_⟩
      rw [hsite, dite_eq_right (by simp only [c] at hxL; omega)]
      omega

/-! ### Injectivity -/

/-- `V(λ)` is the image of the coding. -/
theorem mem_vSet_iff_aCoding {t : ℕ} {μ : YoungDiagram} (h : (vSet t μ).card = t) {x : ℤ} :
    x ∈ vSet t μ ↔ ∃ i, aCoding t μ i = x :=
  ⟨fun hx => aCoding_surj h hx, fun ⟨i, hi⟩ => hi ▸ aCoding_mem h i⟩

/-- **`φ_t` is injective on `t`-cores.** -/
theorem eq_of_vCoding_eq {t : ℕ} (ht : 0 < t) {μ μ' : YoungDiagram} (hμ : IsTCore t μ)
    (hμ' : IsTCore t μ') (h : vCoding t μ = vCoding t μ') : μ = μ' := by
  have hs := stable_of_core ht hμ
  have hs' := stable_of_core ht hμ'
  have ha : aCoding t μ = aCoding t μ' := funext fun i => by
    have := congrFun h i; simp only [vCoding, add_left_inj, Int.cast_inj] at this; exact this
  have hV : ∀ x, x ∈ vSet t μ ↔ x ∈ vSet t μ' := fun x => by
    rw [mem_vSet_iff_aCoding (complete ht hs).card, mem_vSet_iff_aCoding (complete ht hs').card, ha]
  apply eq_of_occ
  intro x
  rw [occ_iff_vSet ht hs, occ_iff_vSet ht hs']
  simp only [hV]

/-! ### Surjectivity -/

/-- **`φ_t` is onto the `V_t`-codings.** -/
theorem exists_of_isVCoding {t : ℕ} (ht : 0 < t) {v : Fin t → ℚ} (hv : IsVCoding t v) :
    ∃ μ, IsTCore t μ ∧ vCoding t μ = v := by
  obtain ⟨hanti, hsum, k, hk, hinj⟩ := hv
  have hkinj : Function.Injective k := fun i j h => hinj i j (by rw [h])
  have hkanti : StrictAnti k := fun i j hij => by
    have := hanti hij; rw [hk, hk] at this; exact_mod_cast (add_lt_add_iff_right _).mp this
  -- the runners' tops form a complete residue system
  have hV : Complete t (univ.image k) := by
    refine ⟨?_, by rw [card_image_of_injective _ hkinj, card_univ, Fintype.card_fin]⟩
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := mem_image.mp hb
    rw [hinj i j hab]
  have hres : ∀ x : ℤ, ∃ i, k i % t = x % t := fun x => by
    have : x % (t : ℤ) ∈ (univ.image k).image (· % (t : ℤ)) := by
      rw [hV.image_emod ht, mem_image]
      have := emod_lt' ht x; have := Int.emod_nonneg x (by omega : (t : ℤ) ≠ 0)
      exact ⟨(x % t).toNat, mem_range.mpr (by omega), by omega⟩
    obtain ⟨a, ha, hax⟩ := mem_image.mp this
    obtain ⟨i, -, rfl⟩ := mem_image.mp ha
    exact ⟨i, hax⟩
  -- the abacus `M = ⋃_i (k_i − tℕ)`
  let M : ℤ → Prop := fun x => ∃ i, ∃ m : ℕ, x = k i - t * m
  set B : ℤ := ∑ i, |k i|
  have hkB : ∀ i, |k i| ≤ B := fun i =>
    single_le_sum (f := fun i => |k i|) (fun _ _ => abs_nonneg _) (mem_univ i)
  have hL : ∀ x < -B, M x := by
    intro x hx
    obtain ⟨i, hi⟩ := hres x
    obtain ⟨m, hm⟩ := emod_eq_iff.mp hi
    have hkx : x < k i := by have := hkB i; have := neg_abs_le (k i); linarith
    have hm0 : 0 ≤ m := by
      by_contra h0; have : (t : ℤ) * m < 0 := mul_neg_of_pos_of_neg (by omega) (by omega)
      linarith
    exact ⟨i, m.toNat, by rw [Int.toNat_of_nonneg hm0]; linarith⟩
  have hU : ∀ x, M x → x ≤ B := by
    rintro x ⟨i, m, rfl⟩
    have := hkB i; have := le_abs_self (k i)
    have : (0 : ℤ) ≤ t * m := by positivity
    linarith
  obtain ⟨μ, c, hμ⟩ := exists_of_maya M (-B) B hL hU
  -- `λ` is a `t`-core
  have hs : Stable t μ := by
    intro x hx
    rw [hμ] at hx ⊢
    obtain ⟨i, m, hm⟩ := hx
    exact ⟨i, m + 1, by push_cast; linarith⟩
  have hcore : IsTCore t μ := (coreStable ht μ).mpr hs
  -- the runner tops of `M`
  have htop : ∀ z, M z ∧ ¬ M (z + t) ↔ ∃ i, k i = z := by
    intro z
    constructor
    · rintro ⟨⟨i, m, rfl⟩, hn⟩
      refine ⟨i, ?_⟩
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · exact absurd ⟨i, m - 1, by push_cast [Nat.cast_sub hm]; ring⟩ hn
    · rintro ⟨i, rfl⟩
      refine ⟨⟨i, 0, by simp⟩, ?_⟩
      rintro ⟨j, m, hm⟩
      have hij : i = j := hinj i j (emod_eq_iff.mpr ⟨-(m : ℤ) - 1, by linarith⟩)
      subst hij
      have : (t : ℤ) * (m + 1) = 0 := by linarith
      have : (0 : ℤ) < t * (m + 1) := by positivity
      linarith
  have hvset : vSet t μ = (univ.image k).image (· - c) := by
    ext y
    rw [mem_vSet, hμ, hμ, show y + t + c = y + c + t by ring, htop]
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨k i, ⟨i, rfl⟩, by linarith⟩
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩; exact ⟨i, by ring⟩
  have hcard : (vSet t μ).card = t := by
    rw [hvset, card_image_of_injective _ (sub_left_injective), hV.card]
  have ha : aCoding t μ = fun i => k i - c := by
    apply eq_of_strictAnti hcard (aCoding_strictAnti hcard)
    · intro i j hij; have := hkanti hij; simp only; omega
    · exact aCoding_mem hcard
    · intro i; rw [hvset]; exact mem_image_of_mem _ (mem_image_of_mem _ (mem_univ i))
  -- the shift `c` vanishes: both codings sum to zero (the second by the charge identity)
  have hsum' := (coding_of_charge (complete ht hs) (charge ht hs)).2.1
  have hvμ : vCoding t μ = fun i => v i - c := funext fun i => by
    simp only [vCoding, ha, hk]; push_cast; ring
  rw [hvμ, sum_sub_distrib, hsum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum'
  have hc : c = 0 := by
    have : (t : ℚ) * c = 0 := by linarith
    exact_mod_cast (mul_eq_zero.mp this).resolve_left (by exact_mod_cast ht.ne')
  refine ⟨μ, hcore, ?_⟩
  rw [hvμ, hc]; simp

/-- **`φ_t` is a bijection from `t`-cores onto `V_t`-codings.** -/
theorem bijective {t : ℕ} (ht : 0 < t) (v : Fin t → ℚ) (hv : IsVCoding t v) :
    ∃! μ, IsTCore t μ ∧ vCoding t μ = v := by
  obtain ⟨μ, hμ, hv'⟩ := exists_of_isVCoding ht hv
  exact ⟨μ, ⟨hμ, hv'⟩, fun μ' ⟨hμ', hv''⟩ =>
    eq_of_vCoding_eq ht hμ' hμ (hv''.trans hv'.symm)⟩

/-- **Dehaye–Han, Theorem 1**, all parts. -/
theorem theorem1 : Theorem1 := theorem1_of_bijective fun _ ht => bijective ht

end

end RMT.MultisetHook
