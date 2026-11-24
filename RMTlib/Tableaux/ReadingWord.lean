import RMTlib.Tableaux.Interlaced
import RMTlib.RSK.RowInsert

/-!
# The reading-word statement

Proof of `RMT.Weyl.ReadingWord` (`readingWord_holds`): for `ν` weakly decreasing, `n ≤ k` and
`m` of weight `ν`, the matrix `m` is interlaced exactly when the recording tableau of its reading
word is `Qnu k ν`, and then the insertion tableau is the filling of `m`.

By `RMT.RSK.Fomin.rskTwoLine_eq`, `rskTwoLine` is bumping RSK of the bottom line. The bottom
line of `readingPairs m` lists the rows of the filling from the bottom up (`bots_eq`).

* Interlacing is column strictness of consecutive rows of the filling (`interlaced_iff`), by
  counting entries `≤ c` in sorted rows.
* **Forward** (`forward`). If the rows `t, …, n - 1` are column strict, inserting them from the
  bottom up rebuilds them (`blocks`, from `RMT.RSK.Fomin.insList_row`), and the boxes created
  depend only on `ν`. So the recording tableau is the same for every interlaced `m`; the
  superstandard filling shows it is `Qnu k ν`.
* **Converse** (`converse`). The entries `≤ n - t` in the first row of the recording tableau
  are as many as the boxes of the first row after inserting the rows `n - 1, …, t`
  (`head_Q_count`). Going up from the bottom, at the first pair of rows `t, t + 1` that is not
  column strict, `RMT.RSK.Fomin.rowFold_bumps_lt` makes that first row longer than `ν t`,
  while for `Qnu k ν` it has length `ν t`.
-/

open Finset

namespace RMT.Weyl

open RMT.RSK RMT.RSK.Fomin RMT.Growth

/-! ### Sorted rows and counts -/

/-- The number of entries `≤ c` of a row. -/
def cnt (u : List ℕ) (c : ℕ) : ℕ := (u.filter (· ≤ c)).length

theorem cnt_le_length (u : List ℕ) (c : ℕ) : cnt u c ≤ u.length := List.length_filter_le _ _

theorem lt_cnt_iff {u : List ℕ} (hu : Sorted u) (c : ℕ) :
    ∀ i, i < u.length → (i < cnt u c ↔ u.getD i 0 ≤ c) := by
  induction u with
  | nil => intro i hi; simp at hi
  | cons z zs ih =>
    intro i hi
    have hz := (List.pairwise_cons.mp hu).1
    have ih := ih (List.pairwise_cons.mp hu).2
    by_cases hzc : z ≤ c
    · cases i with
      | zero => simp [cnt, hzc]
      | succ i =>
        have := ih i (by simpa using hi)
        simp only [cnt] at this ⊢
        simp [hzc, this]
    · have hnil : (z :: zs).filter (· ≤ c) = [] := by
        rw [List.filter_eq_nil_iff]; intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simpa using hzc
        · have := hz a ha; simp; omega
      simp only [cnt, hnil, List.length_nil, Nat.not_lt_zero, false_iff]
      cases i with
      | zero => simpa using hzc
      | succ i =>
        have hmem : zs.getD i 0 ∈ zs := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
          exact List.getElem_mem _
        have := hz _ hmem
        simp only [List.getD_cons_succ]; omega

/-- Column strictness, from counts. -/
theorem col2_of_cnt {u v : List ℕ} {k : ℕ} (hu : Sorted u) (hv : Sorted v)
    (hvk : ∀ x ∈ v, 1 ≤ x ∧ x ≤ k) (h : ∀ a, a < k → cnt v (a + 1) ≤ cnt u a) : Col2 u v := by
  by_cases hv0 : v = []
  · subst hv0; exact ⟨by simp, fun _ hk => by simp at hk⟩
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil v hv0
  have hk : 1 ≤ k := (hvk b hb).1.trans (hvk b hb).2
  refine ⟨?_, ?_⟩
  · have h1 : cnt v k = v.length := by
      simp only [cnt]; rw [List.filter_eq_self.mpr]; intro x hx; simpa using (hvk x hx).2
    have h2 := h (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega, h1] at h2
    exact h2.trans (cnt_le_length u _)
  · intro i hi
    have hmem : v.getD i 0 ∈ v := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem _
    obtain ⟨h1, h2⟩ := hvk _ hmem
    have hc := (lt_cnt_iff hv (v.getD i 0) i hi).mpr (Nat.le_refl _)
    have := h (v.getD i 0 - 1) (by omega)
    rw [show v.getD i 0 - 1 + 1 = v.getD i 0 by omega] at this
    have hiu : i < cnt u (v.getD i 0 - 1) := Nat.lt_of_lt_of_le hc this
    have hil : i < u.length := Nat.lt_of_lt_of_le hiu (cnt_le_length u _)
    have := (lt_cnt_iff hu _ i hil).mp hiu
    omega

/-- Counts, from column strictness. -/
theorem cnt_of_col2 {u v : List ℕ} (hu : Sorted u) (hv : Sorted v) (h : Col2 u v) (c : ℕ) :
    cnt v (c + 1) ≤ cnt u c := by
  suffices ∀ i, i < cnt v (c + 1) → i < cnt u c by
    rcases Nat.eq_zero_or_pos (cnt v (c + 1)) with h0 | hpos
    · omega
    · have := this (cnt v (c + 1) - 1) (by omega); omega
  intro i hi
  have hiv : i < v.length := Nat.lt_of_lt_of_le hi (cnt_le_length v _)
  have h1 := (lt_cnt_iff hv _ i hiv).mp hi
  have h2 := h.2 i hiv
  have hiu : i < u.length := Nat.lt_of_lt_of_le hiv h.1
  exact (lt_cnt_iff hu c i hiu).mpr (by omega)

/-! ### The rows of the filling -/

section
variable {k n : ℕ} (m : Fin k × Fin n → ℕ)

/-- Row `t` of the filling of `m`: `a + 1` repeated `m (a, t)` times (empty for `t ≥ n`). -/
def rowN (t : ℕ) : List ℕ :=
  if h : t < n then (List.finRange k).flatMap fun a => List.replicate (m (a, ⟨t, h⟩)) (a.val + 1)
  else []

theorem rowN_of_lt {t : ℕ} (h : t < n) :
    rowN m t = (List.finRange k).flatMap fun a => List.replicate (m (a, ⟨t, h⟩)) (a.val + 1) := by
  simp [rowN, h]

theorem rowN_sorted (t : ℕ) : Sorted (rowN m t) := by
  unfold rowN; split
  · rw [Sorted, List.pairwise_flatMap]
    refine ⟨fun a _ => ?_, ?_⟩
    · exact List.pairwise_replicate.mpr (Or.inr (Nat.le_refl _))
    · refine (List.pairwise_lt_finRange k).imp fun {a b} hab => ?_
      intro x hx y hy
      rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
      have : a.val < b.val := hab; omega
  · exact List.Pairwise.nil

theorem mem_rowN {t x : ℕ} (hx : x ∈ rowN m t) : 1 ≤ x ∧ x ≤ k := by
  unfold rowN at hx; split at hx
  · simp only [List.mem_flatMap, List.mem_finRange, true_and] at hx
    obtain ⟨a, ha⟩ := hx
    rw [List.eq_of_mem_replicate ha]; omega
  · simp at hx

/-- The entries `≤ c` of row `t` are counted by the matrix. -/
theorem cnt_rowN {t : ℕ} (h : t < n) (c : ℕ) :
    cnt (rowN m t) c = ∑ b : Fin k with b.val < c, m (b, ⟨t, h⟩) := by
  rw [rowN_of_lt m h, cnt, List.filter_flatMap, List.length_flatMap, Finset.sum_filter,
    Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [List.filter_replicate]
  by_cases hac : a.val < c
  · simp [hac, show a.val + 1 ≤ c by omega]
  · simp [hac, show ¬ a.val + 1 ≤ c by omega]

theorem length_rowN {t : ℕ} (h : t < n) : (rowN m t).length = ∑ a : Fin k, m (a, ⟨t, h⟩) := by
  have := cnt_rowN m h k
  rw [cnt, List.filter_eq_self.mpr (fun x hx => by simpa using (mem_rowN m hx).2)] at this
  rw [this]; congr 1; ext b; simp

/-- **Interlacing is column strictness** of consecutive rows of the filling. -/
theorem interlacedAt_iff {t : ℕ} (h : t + 1 < n) :
    InterlacedAt ⟨t, by omega⟩ ⟨t + 1, h⟩ m ↔ Col2 (rowN m t) (rowN m (t + 1)) := by
  have e1 : ∀ a : Fin k, ∑ b : Fin k with b ≤ a, m (b, ⟨t + 1, h⟩) = cnt (rowN m (t + 1)) (a.val + 1) := by
    intro a; rw [cnt_rowN m h]; congr 1
    apply Finset.filter_congr; intro b _; rw [Fin.le_iff_val_le_val]; omega
  have e2 : ∀ a : Fin k, ∑ b : Fin k with b < a, m (b, ⟨t, by omega⟩) = cnt (rowN m t) a.val := by
    intro a; rw [cnt_rowN m (by omega)]; rfl
  unfold InterlacedAt
  simp only [e1, e2]
  constructor
  · intro hI
    exact col2_of_cnt (rowN_sorted m t) (rowN_sorted m (t + 1)) (fun x hx => mem_rowN m hx)
      (fun a ha => hI ⟨a, ha⟩)
  · intro hC a
    exact cnt_of_col2 (rowN_sorted m t) (rowN_sorted m (t + 1)) hC a.val

theorem interlaced_iff : Interlaced m ↔ ∀ t, t + 1 < n → Col2 (rowN m t) (rowN m (t + 1)) := by
  constructor
  · intro hI t ht
    exact (interlacedAt_iff m ht).mp (hI ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl)
  · intro hC l j hj
    obtain ⟨l, hl⟩ := l
    obtain ⟨j, hj'⟩ := j
    simp only at hj; subst hj
    exact (interlacedAt_iff m hj').mpr (hC l hj')

end

/-! ### Inserting the filling block by block -/

section
variable {k n : ℕ} (m : Fin k × Fin n → ℕ) (ν : Fin n → ℕ)

/-- `ν` extended by `0`. -/
def nuN (t : ℕ) : ℕ := if h : t < n then ν ⟨t, h⟩ else 0

/-- The rows `n - 1, …, t` of the filling, concatenated (bottom row first). -/
def botsFrom (t : ℕ) : List ℕ := ((List.range' t (n - t)).reverse).flatMap (rowN m)

/-- The labels of those entries: row `t'` is labelled `n - t'`. -/
def topsNu (t : ℕ) : List ℕ :=
  ((List.range' t (n - t)).reverse).flatMap fun t' => List.replicate (nuN ν t') (n - t')

/-- The nonempty rows `t, …, n - 1` of the filling. -/
def tabFrom (t : ℕ) : Tab := ((List.range' t (n - t)).map (rowN m)).filter (· ≠ [])

/-- The shape of `tabFrom`. -/
def shNu (t : ℕ) : List ℕ := ((List.range' t (n - t)).map (nuN ν)).filter (· ≠ 0)

/-- The rows of the boxes created when inserting the filling: they depend only on `ν`. -/
def boxesNu (t : ℕ) : List ℕ :=
  ((List.range' t (n - t)).reverse).flatMap fun t' => colHeights (shNu ν (t' + 1)) (nuN ν t')

/-- The rows `t - 1, …, 0`, concatenated. -/
def restBots (t : ℕ) : List ℕ := ((List.range' 0 t).reverse).flatMap (rowN m)

/-- Their labels. -/
def restTops (t : ℕ) : List ℕ :=
  ((List.range' 0 t).reverse).flatMap fun t' => List.replicate (nuN ν t') (n - t')

theorem range'_succ_of_lt {t : ℕ} (h : t < n) :
    List.range' t (n - t) = t :: List.range' (t + 1) (n - (t + 1)) := by
  rw [show n - t = n - (t + 1) + 1 by omega, List.range'_succ]

theorem botsFrom_succ {t : ℕ} (h : t < n) : botsFrom m t = botsFrom m (t + 1) ++ rowN m t := by
  simp [botsFrom, range'_succ_of_lt h]

theorem topsNu_succ {t : ℕ} (h : t < n) :
    topsNu ν t = topsNu ν (t + 1) ++ List.replicate (nuN ν t) (n - t) := by
  simp [topsNu, range'_succ_of_lt h]

theorem boxesNu_succ {t : ℕ} (h : t < n) :
    boxesNu ν t = boxesNu ν (t + 1) ++ colHeights (shNu ν (t + 1)) (nuN ν t) := by
  simp [boxesNu, range'_succ_of_lt h]

theorem tabFrom_succ {t : ℕ} (h : t < n) :
    tabFrom m t = if rowN m t = [] then tabFrom m (t + 1) else rowN m t :: tabFrom m (t + 1) := by
  by_cases hr : rowN m t = [] <;> simp [tabFrom, range'_succ_of_lt h, hr]

theorem shNu_succ {t : ℕ} (h : t < n) :
    shNu ν t = if nuN ν t = 0 then shNu ν (t + 1) else nuN ν t :: shNu ν (t + 1) := by
  by_cases hr : nuN ν t = 0 <;> simp [shNu, range'_succ_of_lt h, hr]

theorem of_ge {t : ℕ} (h : n ≤ t) :
    botsFrom m t = [] ∧ topsNu ν t = [] ∧ boxesNu ν t = [] ∧ tabFrom m t = [] ∧ shNu ν t = [] := by
  simp [botsFrom, topsNu, boxesNu, tabFrom, shNu, show n - t = 0 by omega]

theorem length_rowN_eq (hcol : ColSums m ν) (t : ℕ) : (rowN m t).length = nuN ν t := by
  by_cases h : t < n
  · rw [length_rowN m h, hcol ⟨t, h⟩]; simp [nuN, h]
  · simp [rowN, nuN, h]

theorem rowN_eq_nil_iff (hcol : ColSums m ν) (t : ℕ) : rowN m t = [] ↔ nuN ν t = 0 := by
  rw [← length_rowN_eq m ν hcol t, List.length_eq_zero_iff]

theorem nuN_anti (hν : Antitone ν) {t t' : ℕ} (h : t ≤ t') : nuN ν t' ≤ nuN ν t := by
  unfold nuN
  by_cases h' : t' < n
  · rw [dif_pos h', dif_pos (by omega)]; exact hν (show (⟨t, by omega⟩ : Fin n) ≤ ⟨t', h'⟩ from h)
  · rw [dif_neg h']; exact Nat.zero_le _

/-- Below an empty row, everything is empty. -/
theorem tabFrom_eq_nil (hν : Antitone ν) (hcol : ColSums m ν) :
    ∀ d t, t + d = n → rowN m t = [] → tabFrom m t = []
  | 0, t, h, _ => (of_ge m ν (by omega)).2.2.2.1
  | d + 1, t, h, hr => by
    rw [tabFrom_succ m (by omega), if_pos hr]
    apply tabFrom_eq_nil hν hcol d (t + 1) (by omega)
    rw [rowN_eq_nil_iff m ν hcol] at hr ⊢
    have := nuN_anti ν hν (Nat.le_add_right t 1); omega

theorem sh_tabFrom (hcol : ColSums m ν) : ∀ d t, t + d = n → sh (tabFrom m t) = shNu ν t
  | 0, t, h => by rw [(of_ge m ν (by omega)).2.2.2.1, (of_ge m ν (by omega)).2.2.2.2]; rfl
  | d + 1, t, h => by
    rw [tabFrom_succ m (by omega), shNu_succ ν (by omega)]
    have ih := sh_tabFrom hcol d (t + 1) (by omega)
    by_cases hr : rowN m t = []
    · rw [if_pos hr, if_pos ((rowN_eq_nil_iff m ν hcol t).mp hr), ih]
    · rw [if_neg hr, if_neg (fun e => hr ((rowN_eq_nil_iff m ν hcol t).mpr e))]
      simp only [sh, List.map_cons] at ih ⊢
      rw [ih, length_rowN_eq m ν hcol]

/-- **Forward direction, block by block.** If the rows `t, …, n - 1` of the filling are
column strict, inserting them from the bottom up rebuilds them, with boxes `boxesNu ν t`. -/
theorem blocks (hν : Antitone ν) (hcol : ColSums m ν) : ∀ d t, t + d = n →
    (∀ t', t ≤ t' → t' + 1 < n → Col2 (rowN m t') (rowN m (t' + 1))) →
    SSYT (tabFrom m t) ∧ insList [] (botsFrom m t) = (tabFrom m t, boxesNu ν t)
  | 0, t, h, _ => by
    obtain ⟨h1, -, h3, h4, -⟩ := of_ge m ν (show n ≤ t by omega)
    rw [h1, h3, h4]
    exact ⟨⟨fun r hr => by simp at hr, trivial⟩, rfl⟩
  | d + 1, t, h, hC => by
    have ht : t < n := by omega
    obtain ⟨ih1, ih2⟩ := blocks hν hcol d (t + 1) (by omega) (fun t' h1 h2 => hC t' (by omega) h2)
    rw [botsFrom_succ m ht, insList_append, ih2, tabFrom_succ m ht, boxesNu_succ ν ht]
    simp only
    by_cases hr : rowN m t = []
    · rw [if_pos hr, hr]
      have : nuN ν t = 0 := (rowN_eq_nil_iff m ν hcol t).mp hr
      rw [this]
      exact ⟨ih1, by simp [insList, colHeights]⟩
    · rw [if_neg hr]
      have hss : SSYT (rowN m t :: tabFrom m (t + 1)) := by
        refine ⟨?_, ?_⟩
        · intro r hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact ⟨rowN_sorted m t, hr⟩
          · exact ih1.good r hr'
        · cases htf : tabFrom m (t + 1) with
          | nil => trivial
          | cons s rest =>
            rw [htf] at ih1
            have ht1 : t + 1 < n := by
              by_contra hc
              rw [(of_ge m ν (show n ≤ t + 1 by omega)).2.2.2.1] at htf; simp at htf
            have hr1 : rowN m (t + 1) ≠ [] := fun e => by
              rw [tabFrom_eq_nil m ν hν hcol (d) (t + 1) (by omega) e] at htf; simp at htf
            have hs : s = rowN m (t + 1) := by
              rw [tabFrom_succ m ht1, if_neg hr1] at htf; exact (List.cons.inj htf).1.symm
            subst hs
            exact ⟨hC t (Nat.le_refl _) ht1, ih1.2⟩
      refine ⟨hss, ?_⟩
      rw [insList_row _ _ hss, sh_tabFrom m ν hcol d (t + 1) (by omega), length_rowN_eq m ν hcol]

end

/-! ### `readingPairs` and `tableauOf` in terms of the rows -/

section
variable {k n : ℕ} (m : Fin k × Fin n → ℕ) (ν : Fin n → ℕ)

theorem map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range' 0 n := by
  apply List.ext_getElem <;> simp

theorem flatMap_finRange_reverse {α : Type*} (g : ℕ → List α) :
    (List.finRange n).reverse.flatMap (fun t => g t.val) = (List.range' 0 n).reverse.flatMap g := by
  rw [← map_val_finRange, ← List.map_reverse, List.flatMap_map]

theorem inner_snd (t : Fin n) :
    ((List.finRange k).flatMap fun a => List.replicate (m (a, t)) (n - t.val, a.val + 1)).map (·.2)
      = rowN m t.val := by
  rw [rowN_of_lt m t.isLt, List.map_flatMap]; simp [List.map_replicate]

theorem inner_fst (t : Fin n) :
    ((List.finRange k).flatMap fun a => List.replicate (m (a, t)) (n - t.val, a.val + 1)).map (·.1)
      = List.replicate (rowN m t.val).length (n - t.val) := by
  rw [List.eq_replicate_iff]
  refine ⟨?_, ?_⟩
  · rw [← inner_snd m t, List.length_map, List.length_map]
  · intro b hb
    simp only [List.mem_map, List.mem_flatMap, List.mem_finRange, true_and] at hb
    obtain ⟨p, ⟨a, ha⟩, rfl⟩ := hb
    rw [List.eq_of_mem_replicate ha]

theorem bots_eq : (readingPairs m).map (·.2) = botsFrom m 0 := by
  rw [readingPairs, List.map_flatMap]
  simp only [inner_snd]
  rw [flatMap_finRange_reverse (fun t => rowN m t)]
  simp [botsFrom]

theorem tops_eq (hcol : ColSums m ν) : (readingPairs m).map (·.1) = topsNu ν 0 := by
  rw [readingPairs, List.map_flatMap]
  simp only [inner_fst]
  rw [flatMap_finRange_reverse (fun t => List.replicate (rowN m t).length (n - t))]
  simp [topsNu, length_rowN_eq m ν hcol]

theorem tableauOf_eq : tableauOf m = tabFrom m 0 := by
  have : (List.finRange n).map (fun t => (List.finRange k).flatMap fun a =>
      List.replicate (m (a, t)) (a.val + 1)) = (List.range' 0 n).map (rowN m) := by
    rw [← map_val_finRange, List.map_map]
    apply List.map_congr_left; intro t _; simp [rowN_of_lt m t.isLt]
  simp [tableauOf, tabFrom, this]

/-- `rskTwoLine` of the reading pairs, as bumping on the bottom line. -/
theorem rskTwoLine_readingPairs :
    rskTwoLine (readingPairs m) = ((insList [] ((readingPairs m).map (·.2))).1,
      qFrom [] ((readingPairs m).map (·.1)) (insList [] ((readingPairs m).map (·.2))).2) := by
  rw [rskTwoLine_eq, insT_eq _ _ (by simp), recL_eq _ _ _ (by simp) (by simp)]
  have h1 : ∀ f : ℕ × ℕ → ℕ, ((readingPairs m).map f).take (readingPairs m).length =
      (readingPairs m).map f := fun f => List.take_of_length_le (by simp)
  simp only [h1]

/-! ### The superstandard filling -/

theorem colSums_superstandard (hnk : n ≤ k) : ColSums (superstandard (k := k) ν) ν := by
  intro t
  have : ∀ a : Fin k, superstandard (k := k) ν (a, t) =
      if a = ⟨t.val, by omega⟩ then ν t else 0 := by
    intro a; simp [superstandard, Fin.ext_iff]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mem_rowN_superstandard {t x : ℕ} (hx : x ∈ rowN (superstandard (k := k) ν) t) :
    x = t + 1 := by
  unfold rowN at hx; split at hx
  · simp only [List.mem_flatMap, List.mem_finRange, true_and] at hx
    obtain ⟨a, ha⟩ := hx
    have hpos : superstandard (k := k) ν (a, ⟨t, by omega⟩) ≠ 0 := by
      intro h0; rw [h0] at ha; simp at ha
    rw [List.eq_of_mem_replicate ha]
    simp only [superstandard] at hpos
    split at hpos
    · rename_i h; have : a.val = t := h; omega
    · exact absurd rfl hpos
  · simp at hx

theorem col2_superstandard (hν : Antitone ν) (hnk : n ≤ k) (t : ℕ) :
    Col2 (rowN (superstandard (k := k) ν) t) (rowN (superstandard (k := k) ν) (t + 1)) := by
  have hcol := colSums_superstandard ν hnk
  refine ⟨?_, ?_⟩
  · rw [length_rowN_eq _ ν hcol, length_rowN_eq _ ν hcol]
    exact nuN_anti ν hν (Nat.le_add_right t 1)
  · intro i hi
    have hlen : (rowN (superstandard (k := k) ν) (t + 1)).length ≤
        (rowN (superstandard (k := k) ν) t).length := by
      rw [length_rowN_eq _ ν hcol, length_rowN_eq _ ν hcol]
      exact nuN_anti ν hν (Nat.le_add_right t 1)
    rw [getD_of_lt (by omega), getD_of_lt hi,
      mem_rowN_superstandard ν (List.getElem_mem _), mem_rowN_superstandard ν (List.getElem_mem _)]
    omega

end

/-! ### Both directions -/

section
variable {k n : ℕ} (m : Fin k × Fin n → ℕ) (ν : Fin n → ℕ)

/-- The recording tableau of every interlaced matrix of weight `ν`. -/
def Qν : Tab := qFrom [] (topsNu ν 0) (boxesNu ν 0)

/-- **Forward direction.** An interlaced matrix inserts back to its filling, with the recording
tableau `Qν ν`. -/
theorem forward (hν : Antitone ν) (hcol : ColSums m ν) (hI : Interlaced m) :
    rskTwoLine (readingPairs m) = (tableauOf m, Qν ν) := by
  have hC := (interlaced_iff m).mp hI
  obtain ⟨-, h⟩ := blocks m ν hν hcol n 0 (by omega) (fun t' _ ht => hC t' ht)
  rw [rskTwoLine_readingPairs, bots_eq, tops_eq m ν hcol, h, tableauOf_eq]; rfl

theorem Qnu_eq (hν : Antitone ν) (hnk : n ≤ k) : Qnu k ν = Qν ν := by
  have := forward (superstandard (k := k) ν) ν hν (colSums_superstandard ν hnk)
    ((interlaced_iff _).mpr fun t _ => col2_superstandard ν hν hnk t)
  simp only [Qnu, this]

theorem botsFrom_split {t : ℕ} (ht : t ≤ n) : botsFrom m 0 = botsFrom m t ++ restBots m t := by
  have : List.range' 0 n = List.range' 0 t ++ List.range' t (n - t) := by
    have := List.range'_append (s := 0) (m := t) (n := n - t) (step := 1)
    simp only [Nat.zero_add, Nat.one_mul] at this
    rw [Nat.add_sub_cancel' ht] at this; exact this.symm
  simp [botsFrom, restBots, this]

theorem topsNu_split {t : ℕ} (ht : t ≤ n) : topsNu ν 0 = topsNu ν t ++ restTops ν t := by
  have : List.range' 0 n = List.range' 0 t ++ List.range' t (n - t) := by
    have := List.range'_append (s := 0) (m := t) (n := n - t) (step := 1)
    simp only [Nat.zero_add, Nat.one_mul] at this
    rw [Nat.add_sub_cancel' ht] at this; exact this.symm
  simp [topsNu, restTops, this]

theorem length_topsNu (hcol : ColSums m ν) (t : ℕ) :
    (topsNu ν t).length = (botsFrom m t).length := by
  simp only [topsNu, botsFrom, List.length_flatMap, List.length_replicate]
  congr 1; apply List.map_congr_left; intro t' _; rw [length_rowN_eq m ν hcol]

/-- The first row of `Q`, below the label `n - t`, is as long as the first row after inserting
the rows `n - 1, …, t`. -/
theorem head_Q_count (hcol : ColSums m ν) {t : ℕ} (ht : t ≤ n) :
    ((((rskTwoLine (readingPairs m)).2).headD []).filter (· ≤ n - t)).length =
      ((insList [] (botsFrom m t)).1.headD []).length := by
  rw [rskTwoLine_readingPairs, bots_eq, tops_eq m ν hcol, botsFrom_split m ht, topsNu_split ν ht]
  apply qFrom_head_count _ _ _ _ _ (length_topsNu m ν hcol t)
  · intro l hl
    simp only [topsNu, List.mem_flatMap, List.mem_reverse, List.mem_range'_1] at hl
    obtain ⟨t', ht', hl⟩ := hl
    rw [List.eq_of_mem_replicate hl]; omega
  · intro l hl
    simp only [restTops, List.mem_flatMap, List.mem_reverse, List.mem_range'_1] at hl
    obtain ⟨t', ht', hl⟩ := hl
    rw [List.eq_of_mem_replicate hl]; omega

/-- **Converse.** If the recording tableau is `Qν ν`, the matrix is interlaced. -/
theorem converse (hν : Antitone ν) (hnk : n ≤ k) (hcol : ColSums m ν)
    (hQ : (rskTwoLine (readingPairs m)).2 = Qν ν) : Interlaced m := by
  set m₀ := superstandard (k := k) ν
  have hcol₀ := colSums_superstandard ν hnk
  have hQ₀ : (rskTwoLine (readingPairs m₀)).2 = Qν ν := by
    rw [forward m₀ ν hν hcol₀ ((interlaced_iff _).mpr fun t _ => col2_superstandard ν hν hnk t)]
  -- the first row after the rows `n - 1, …, t`, for the superstandard filling
  have hrow₀ : ∀ t, t < n → ((insList [] (botsFrom m₀ t)).1.headD []).length = nuN ν t := by
    intro t ht
    obtain ⟨-, h⟩ := blocks m₀ ν hν hcol₀ (n - t) t (by omega)
      (fun t' _ _ => col2_superstandard ν hν hnk t')
    rw [h, tabFrom_succ m₀ ht]
    by_cases hr : rowN m₀ t = []
    · rw [if_pos hr, tabFrom_eq_nil m₀ ν hν hcol₀ (n - (t + 1)) (t + 1) (by omega)]
      · simp; exact ((rowN_eq_nil_iff m₀ ν hcol₀ t).mp hr).symm
      · rw [rowN_eq_nil_iff m₀ ν hcol₀] at hr ⊢
        have := nuN_anti ν hν (Nat.le_add_right t 1); omega
    · rw [if_neg hr]; exact length_rowN_eq m₀ ν hcol₀ t
  have hrow : ∀ t, t < n → ((insList [] (botsFrom m t)).1.headD []).length = nuN ν t := by
    intro t ht
    rw [← head_Q_count m ν hcol (Nat.le_of_lt ht), hQ, ← hQ₀, head_Q_count m₀ ν hcol₀ (Nat.le_of_lt ht)]
    exact hrow₀ t ht
  rw [interlaced_iff]
  suffices ∀ d t, t + d = n → ∀ t', t ≤ t' → t' + 1 < n → Col2 (rowN m t') (rowN m (t' + 1)) from
    fun t' ht' => this n 0 (by omega) t' (Nat.zero_le _) ht'
  intro d
  induction d with
  | zero => intro t h t' ht' ht''; omega
  | succ d ih =>
    intro t h t' ht' ht''
    rcases Nat.eq_or_lt_of_le ht' with rfl | hlt
    · clear ht'
      have ih' := ih (t + 1) (by omega)
      by_contra hC
      set u := rowN m t
      set v := rowN m (t + 1)
      have hlen : v.length ≤ u.length := by
        rw [length_rowN_eq m ν hcol, length_rowN_eq m ν hcol]
        exact nuN_anti ν hν (Nat.le_add_right t 1)
      have hex : ∃ i, i < v.length ∧ ¬ u.getD i 0 < v.getD i 0 := by
        by_contra hne
        exact hC ⟨hlen, fun i hi => by
          by_contra h; exact hne ⟨i, hi, h⟩⟩
      have hv : v ≠ [] := by
        intro e; obtain ⟨i, hi, -⟩ := hex; rw [e] at hi; simp at hi
      obtain ⟨-, hF⟩ := blocks m ν hν hcol d (t + 1) (by omega) ih'
      have htab : tabFrom m (t + 1) = v :: tabFrom m (t + 2) := by
        rw [tabFrom_succ m ht'', if_neg hv]
      have hins : (insList [] (botsFrom m t)).1 = (insList (v :: tabFrom m (t + 2)) u).1 := by
        rw [botsFrom_succ m (by omega), insList_append, hF, htab]
      obtain ⟨rest', hrest⟩ := insList_head u v (tabFrom m (t + 2))
      have hr := hrow t (by omega)
      rw [hins, hrest] at hr
      simp only [List.headD_cons] at hr
      -- the first column where `u` fails to sit on `v`
      classical
      set j0 := Nat.find hex with hj0d
      have hj0 : j0 < v.length ∧ ¬ u.getD j0 0 < v.getD j0 0 := Nat.find_spec hex
      have hmin : ∀ i, i < j0 → u.getD i 0 < v.getD i 0 := by
        intro i hi
        have := Nat.find_min hex hi
        by_contra h; exact this ⟨by omega, h⟩
      have hb : nBumps (rowFold v u).2 < v.length := rowFold_bumps_lt (rowN_sorted m t) hj0.1 (Nat.lt_of_lt_of_le hj0.1 hlen) hmin
        (Nat.le_of_not_lt hj0.2)
      have hl := rowFold_length u v
      have : u.length = nuN ν t := length_rowN_eq m ν hcol t
      omega
    · exact ih (t + 1) (by omega) t' hlt ht''

/-- **The reading-word statement holds.** -/
theorem readingWord_holds : ReadingWord := by
  intro k n ν hν hnk m hcol
  rw [Qnu_eq ν hν hnk]
  refine ⟨⟨fun hI => by rw [forward m ν hν hcol hI], converse m ν hν hnk hcol⟩, fun hI => ?_⟩
  rw [forward m ν hν hcol hI]

end

end RMT.Weyl
