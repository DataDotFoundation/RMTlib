import RMTlib.Tableaux.Yamanouchi
import RMTlib.Tableaux.Square

/-!
# The hook-length formula for the square

`HookLengthSquare`: the number `g_k` of standard Young tableaux of the `k × k` square is
`(k²)! · ksConst k = (k²)! ∏_{j<k} j!/(j+k)!`.

* `squareSYTEquiv`: square fillings (`IsSquareSYT`) are Yamanouchi words of square shape.
  The word of a filling lists the row of each entry `0, 1, 2, …`. The filling of a word puts in
  cell `(i, j)` the position of the `j`-th letter `i`.
* `gSYT_eq_fSYT`: hence `g_k = f^{k×k}` (with `RMT.card_isYam`).
* `hookLengthSquare_holds`: with `RMT.hook_length_formula` and Frobenius's identity,
  `H(k×k) · ∏_{j<k} j! = ∏_{j<k} (j+k)!`.

So `g_k/(k²)!` (the Plancherel weight of the square, `1/‖hw_{k×k}‖²_Fock`) is the
Keating–Snaith constant.
-/

open Finset
open scoped Nat

namespace RMT

/-! ### Ranks in a finite set of `Fin n` -/

theorem card_lt_orderEmbOfFin {n : ℕ} (S : Finset (Fin n)) {k : ℕ} (h : #S = k) (j : Fin k) :
    #{s ∈ S | s < S.orderEmbOfFin h j} = j := by
  have : {s ∈ S | s < S.orderEmbOfFin h j} = (Iio j).map (S.orderEmbOfFin h).toEmbedding := by
    ext s
    simp only [mem_filter, mem_map, mem_Iio]
    constructor
    · rintro ⟨hs, hlt⟩
      obtain ⟨j', rfl⟩ : s ∈ Set.range (S.orderEmbOfFin h) := by
        rw [range_orderEmbOfFin]; exact hs
      exact ⟨j', (S.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j', hj', rfl⟩
      exact ⟨orderEmbOfFin_mem _ _ _, (S.orderEmbOfFin h).lt_iff_lt.mpr hj'⟩
  rw [this, card_map, Fin.card_Iio]

theorem eq_orderEmbOfFin_of_rank {n : ℕ} (S : Finset (Fin n)) {k : ℕ} (h : #S = k) (j : Fin k)
    {t : Fin n} (ht : t ∈ S) (hr : #{s ∈ S | s < t} = j) : t = S.orderEmbOfFin h j := by
  obtain ⟨j', rfl⟩ : t ∈ Set.range (S.orderEmbOfFin h) := by rw [range_orderEmbOfFin]; exact ht
  rw [card_lt_orderEmbOfFin] at hr
  rw [Fin.ext hr]

/-! ### Letter counts -/

variable {N : ℕ}

theorem cnt_eq_card {n : ℕ} (w : Fin n → Fin N) (t : ℕ) (i : Fin N) :
    cnt w t i = #(univ.filter fun s : Fin n => s.val < t ∧ w s = i) := by
  simp [cnt, sum_boole]

theorem cnt_succ {n : ℕ} (w : Fin n → Fin N) (t : Fin n) (i : Fin N) :
    cnt w (t.val + 1) i = cnt w t.val i + if w t = i then 1 else 0 := by
  simp only [cnt]
  rw [show (if w t = i then 1 else 0) = ∑ s, if s = t ∧ w s = i then 1 else 0 by
    rw [Fintype.sum_eq_single t fun s hs => by simp [hs]]; simp, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : s = t
  · subst hs; simp
  · have : s.val ≠ t.val := fun e => hs (Fin.ext e)
    by_cases h' : s.val < t.val <;> simp [hs, h', show (s.val < t.val + 1 ↔ s.val < t.val) by omega]

theorem cnt_mono {n : ℕ} (w : Fin n → Fin N) {t t' : ℕ} (h : t ≤ t') (i : Fin N) :
    cnt w t i ≤ cnt w t' i :=
  sum_le_sum fun s _ => by split_ifs with h1 h2 <;> omega

/-! ### Square fillings are Yamanouchi words -/

/-- The `k × k` square. -/
def sq (k : ℕ) : Fin k → ℕ := fun _ => k

variable {k : ℕ}

/-- The word of a filling: letter `t` is the row holding the entry `t`. -/
noncomputable def wordOf (f : Fin k × Fin k → Fin (k * k)) (hf : Function.Bijective f) :
    Fin (k * k) → Fin k :=
  fun t => ((Equiv.ofBijective f hf).symm t).1

theorem wordOf_apply (f : Fin k × Fin k → Fin (k * k)) (hf : Function.Bijective f) (c) :
    wordOf f hf (f c) = c.1 := by
  simp only [wordOf]
  rw [show f c = Equiv.ofBijective f hf c from rfl, Equiv.symm_apply_apply]

theorem cnt_wordOf (f : Fin k × Fin k → Fin (k * k)) (hf : Function.Bijective f) (t : ℕ)
    (i : Fin k) : cnt (wordOf f hf) t i = #(univ.filter fun j : Fin k => (f (i, j)).val < t) := by
  have hinj : Function.Injective fun j : Fin k => f (i, j) :=
    fun j j' h => (Prod.mk.inj (hf.1 h)).2
  rw [cnt_eq_card, ← card_image_of_injective _ hinj]
  congr 1
  ext s
  simp only [mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨hs, hw⟩
    set c := (Equiv.ofBijective f hf).symm s with hc
    have hfc : f c = s := Equiv.ofBijective_apply_symm_apply f hf s
    have hc1 : c.1 = i := hw
    refine ⟨c.2, ?_, ?_⟩
    · rw [← hc1, Prod.mk.eta, hfc]; exact hs
    · rw [← hc1, Prod.mk.eta, hfc]
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hj, wordOf_apply f hf (i, j)⟩

theorem isYam_wordOf {f : Fin k × Fin k → Fin (k * k)} (hf : IsSquareSYT k f) :
    IsYam (sq k) (wordOf f hf.1) := by
  refine ⟨fun t i i' hii' => ?_, ?_⟩
  · rw [cnt_wordOf, cnt_wordOf]
    refine card_le_card fun j => ?_
    simp only [mem_filter, mem_univ, true_and]
    intro h
    rcases eq_or_lt_of_le hii' with rfl | hlt
    · exact h
    · exact lt_trans (hf.2.2 i i' j hlt) h
  · funext i
    rw [cnt_wordOf]
    simp [sq]

section fill

variable (w : Fin (k * k) → Fin k) (hw : IsYam (sq k) w)

/-- The entries of row `i`: the positions of the letter `i`. -/
def rowSet (i : Fin k) : Finset (Fin (k * k)) := {s | w s = i}

include hw in
theorem card_rowSet (i : Fin k) : #(rowSet w i) = k := by
  have := congrFun hw.2 i
  rw [cnt_eq_card] at this
  simpa [rowSet, sq] using this

/-- The filling of a word: entry `(i, j)` is the position of the `j`-th letter `i`. -/
noncomputable def fillOf : Fin k × Fin k → Fin (k * k) :=
  fun c => (rowSet w c.1).orderEmbOfFin (card_rowSet w hw c.1) c.2

theorem word_fillOf (c : Fin k × Fin k) : w (fillOf w hw c) = c.1 := by
  have := orderEmbOfFin_mem (rowSet w c.1) (card_rowSet w hw c.1) c.2
  simp only [rowSet, mem_filter, mem_univ, true_and] at this
  exact this

theorem cnt_fillOf (i j : Fin k) : cnt w (fillOf w hw (i, j)).val i = j := by
  rw [cnt_eq_card, ← card_lt_orderEmbOfFin (rowSet w i) (card_rowSet w hw i) j]
  refine congrArg Finset.card ?_
  change _ = {s ∈ rowSet w i | s < fillOf w hw (i, j)}
  generalize fillOf w hw (i, j) = u
  ext s
  simp only [rowSet, mem_filter, mem_univ, true_and]
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨b, a⟩

theorem isSquareSYT_fillOf : IsSquareSYT k (fillOf w hw) := by
  have hinj : Function.Injective (fillOf w hw) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hi : i = i' := by
      have := congrArg w h
      rwa [word_fillOf w hw, word_fillOf w hw] at this
    subst hi
    have := (rowSet w i).orderEmbOfFin (card_rowSet w hw i) |>.injective h
    simp only at this
    rw [this]
  refine ⟨(Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩,
    fun i j j' h => ((rowSet w i).orderEmbOfFin _).lt_iff_lt.mpr h, fun i i' j h => ?_⟩
  by_contra hle
  push Not at hle
  set t := fillOf w hw (i', j)
  set u := fillOf w hw (i, j)
  have hwt : w t = i' := word_fillOf w hw _
  have htu : t < u := lt_of_le_of_ne hle fun e => by
    have : w u = i := word_fillOf w hw (i, j)
    rw [← e, hwt] at this
    exact h.ne this.symm
  have hA := hw.1 (t.val + 1) h.le
  rw [cnt_succ, cnt_succ, hwt, ite_eq_left rfl, ite_eq_right h.ne', cnt_fillOf] at hA
  have := cnt_mono w (Fin.lt_def.mp htu).le i
  rw [cnt_fillOf] at this
  omega

theorem wordOf_fillOf : wordOf (fillOf w hw) (isSquareSYT_fillOf w hw).1 = w := by
  funext t
  set e := Equiv.ofBijective _ (isSquareSYT_fillOf w hw).1
  have : fillOf w hw (e.symm t) = t := Equiv.ofBijective_apply_symm_apply _ _ t
  simp only [wordOf]
  conv_rhs => rw [← this]
  rw [word_fillOf w hw]

end fill

theorem fillOf_wordOf {f : Fin k × Fin k → Fin (k * k)} (hf : IsSquareSYT k f) :
    fillOf (wordOf f hf.1) (isYam_wordOf hf) = f := by
  funext ⟨i, j⟩
  symm
  show f (i, j) = (rowSet _ i).orderEmbOfFin _ j
  refine eq_orderEmbOfFin_of_rank _ _ _ (by simp [rowSet, wordOf_apply]) ?_
  have hr := cnt_wordOf f hf.1 (f (i, j)).val i
  rw [cnt_eq_card] at hr
  have e1 : {s ∈ rowSet (wordOf f hf.1) i | s < f (i, j)} =
      univ.filter (fun s : Fin (k * k) => s.val < (f (i, j)).val ∧ wordOf f hf.1 s = i) := by
    ext s
    simp only [rowSet, mem_filter, mem_univ, true_and]
    constructor <;> rintro ⟨a, b⟩ <;> exact ⟨b, a⟩
  have e2 : univ.filter (fun j' : Fin k => (f (i, j')).val < (f (i, j)).val) = Iio j := by
    ext j'
    simp only [mem_filter, mem_univ, true_and, mem_Iio]
    constructor
    · intro hlt
      by_contra hge
      push Not at hge
      rcases eq_or_lt_of_le hge with rfl | hlt'
      · exact lt_irrefl _ hlt
      · exact absurd (hf.2.1 i j j' hlt') (not_lt.mpr (Fin.le_def.mpr hlt.le))
    · intro hlt; exact Fin.lt_def.mp (hf.2.1 i j' j hlt)
  rw [e1, hr, e2, Fin.card_Iio]

/-- Square standard Young tableaux are Yamanouchi words of square shape. -/
noncomputable def squareSYTEquiv : {f // IsSquareSYT k f} ≃ {w : Fin (k * k) → Fin k // IsYam (sq k) w} where
  toFun f := ⟨wordOf f.1 f.2.1, isYam_wordOf f.2⟩
  invFun w := ⟨fillOf w.1 w.2, isSquareSYT_fillOf w.1 w.2⟩
  left_inv f := Subtype.ext (fillOf_wordOf f.2)
  right_inv w := Subtype.ext (wordOf_fillOf w.1 w.2)

theorem sum_sq : ∑ i, sq k i = k * k := by simp [sq]

/-- `g_k = f^{k×k}`: the fillings count equals the path count. -/
theorem gSYT_eq_fSYT : gSYT k = fSYT (k * k) (sq k) := by
  rw [gSYT, ← Nat.card_eq_fintype_card, Nat.card_congr squareSYTEquiv,
    card_isYam _ (sq k) (fun _ _ _ => le_rfl) sum_sq]

/-! ### The hook product of the square -/

theorem prod_Ioi_sub (i : Fin k) : ∏ j ∈ Ioi i, ((j : ℕ) - i) = (k - 1 - i)! := by
  have e := prod_map (Ioi i) Fin.valEmbedding (fun m => m - (i : ℕ))
  simp only [Fin.valEmbedding_apply] at e
  rw [← e, Fin.map_valEmbedding_Ioi,
    ← Finset.Ico_add_one_left_eq_Ioo, prod_Ico_eq_prod_range, ← prod_range_add_one_eq_factorial]
  have := i.isLt
  rw [show k - ((i : ℕ) + 1) = k - 1 - i by omega]
  exact prod_congr rfl fun d _ => by omega

/-- **The hook-length formula for squares** (Frame–Robinson–Thrall):
`g_k = (k²)! · ∏_{j<k} j!/(j+k)!`. -/
theorem hookLengthSquare_holds : HookLengthSquare := by
  intro k
  rw [hookLengthSquare_iff, gSYT_eq_fSYT]
  have hH := hook_length_formula (sq k) (fun _ _ _ => le_rfl)
  rw [sum_sq] at hH
  have hF := frobenius (sq k) (fun _ _ _ => le_rfl)
  have hV : ∏ i : Fin k, ∏ j ∈ Ioi i, (sq k i - sq k j + ((j : ℕ) - i)) = ∏ j ∈ range k, j ! := by
    simp only [sq, Nat.sub_self, zero_add, prod_Ioi_sub]
    rw [Fin.prod_univ_eq_prod_range (fun i => (k - 1 - i)!) k,
      prod_range_reflect (fun j => j !) k]
  have hL : ∏ i : Fin k, (sq k i + (k - 1 - i))! = ∏ j ∈ range k, (j + k)! := by
    simp only [sq]
    rw [Fin.prod_univ_eq_prod_range (fun i => (k + (k - 1 - i))!) k,
      ← prod_range_reflect (fun j => (j + k)!) k]
    exact prod_congr rfl fun j _ => by rw [add_comm]
  rw [hV, hL] at hF
  rw [← hF, ← mul_assoc, hH]

end RMT
