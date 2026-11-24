import RMTlib.Symmetric.Cauchy
import Mathlib.Combinatorics.Young.SemistandardTableau

/-!
# Chains of horizontal strips and Mathlib's semistandard Young tableaux

`RMT.Symmetric.Tab N m` represents a semistandard tableau with entries `< m` as a chain of
horizontal strips of padded shapes. This file identifies it with Mathlib's
`SemistandardYoungTableau μ` whose entries are `< m`, for a Young diagram `μ` with at most `N`
rows, and identifies the weights. The Schur polynomial of `RMT.Symmetric.Cauchy` is then the
total weight of Mathlib's tableaux (`schur_eq_schurSSYT`), and the Cauchy identity can be stated
as a sum over Young diagrams (`cauchy_ssyt`).

* `rowsOf N μ`: the row lengths of `μ`, padded to `N`.
* `toSSYT`: the entry of a box is the step of the chain at which it is added.
* `ofSSYT`: the chain `j ↦ shape of the entries < j`.
* `ssytWt x T`: `Σ_{(i, j) ∈ μ} x_{T i j}`.
* `schurSSYT R x m μ`: `∑' T : SSYT μ with entries < m, X ^ (ssytWt x T)`.

## Main results

* `tabEquiv`: `{T : Tab N m // T.shape = rowsOf N μ} ≃ {T : SSYT μ // entries < m}`, for `μ`
  with at most `N` rows.
* `wt_ofSSYT`: the equivalence preserves weights.
* `schur_eq_schurSSYT`: the Schur polynomial of `RMT.Symmetric.Cauchy` is `schurSSYT`.
* `cauchy_ssyt`, `cauchy_prod_ssyt`: the Cauchy identity summed over all Young diagrams `μ`,
  with Mathlib's tableaux.
-/

open scoped MvPowerSeries.WithPiTopology
open MvPowerSeries

namespace RMT.Symmetric

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthSuper (HStrip size)
open RMT.RSK.GrowthBij (IsHChain)

/-! ## Horizontal strips, index by index -/

/-- `b / a` is a horizontal strip iff, row by row, `a_r ≤ b_r` and `b_{r+1} ≤ a_r`. -/
theorem hstrip_iff : ∀ a b : Part, HStrip a b ↔
    a.length = b.length ∧ ∀ r, a.getD r 0 ≤ b.getD r 0 ∧ b.getD (r + 1) 0 ≤ a.getD r 0
  | [], [] => by simp [HStrip]
  | [x], [y] => by
    simp only [HStrip, List.length_cons, List.length_nil, true_and]
    constructor
    · intro h r
      cases r with
      | zero => simpa using h
      | succ r => simp
    · intro h
      simpa using (h 0).1
  | x :: x' :: as, y :: y' :: bs => by
    rw [show HStrip (x :: x' :: as) (y :: y' :: bs) ↔
      x ≤ y ∧ y' ≤ x ∧ HStrip (x' :: as) (y' :: bs) from Iff.rfl, hstrip_iff (x' :: as) (y' :: bs)]
    constructor
    · rintro ⟨h1, h2, hl, h⟩
      refine ⟨by simpa using hl, fun r => ?_⟩
      cases r with
      | zero => exact ⟨h1, h2⟩
      | succ r => simpa using h r
    · rintro ⟨hl, h⟩
      exact ⟨(h 0).1, (h 0).2, by simpa using hl, fun r => by simpa using h (r + 1)⟩
  | [], _ :: _ | _ :: _, [] | [_], _ :: _ :: _ | _ :: _ :: _, [_] => by simp [HStrip]

theorem list_ext_getD {l l' : Part} (hl : l.length = l'.length)
    (h : ∀ r, l.getD r 0 = l'.getD r 0) : l = l' := by
  apply List.ext_getElem hl
  intro r h1 h2
  have := h r
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] using this

section ChainFacts

variable {N m : ℕ} {c : ℕ → Part}

theorem chain_mono (h : IsHChain N m c) (r : ℕ) {j j' : ℕ} (hjj : j ≤ j') (hj' : j' ≤ m) :
    (c j).getD r 0 ≤ (c j').getD r 0 := by
  induction hjj with
  | refl => exact Nat.le_refl _
  | step hle ih =>
    exact Nat.le_trans (ih (by omega)) (((hstrip_iff _ _).1 (h.2 _ (by omega))).2 r).1

theorem chain_strip (h : IsHChain N m c) (r : ℕ) {j : ℕ} (hj : j < m) :
    (c (j + 1)).getD (r + 1) 0 ≤ (c j).getD r 0 :=
  (((hstrip_iff _ _).1 (h.2 j hj)).2 r).2

theorem chain_zero (h : IsHChain N m c) (r : ℕ) : (c 0).getD r 0 = 0 := by
  rw [h.1]
  simp [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

end ChainFacts

/-! ## Counting in a downward-closed set -/

/-- In a downward-closed subset of `[0, L)`, at most `k` elements iff `k` is not in it. -/
theorem card_filter_le_iff {L k : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hP : ∀ x y, x ≤ y → y < L → P y → P x) (hk : k < L) :
    ((Finset.range L).filter P).card ≤ k ↔ ¬ P k := by
  constructor
  · intro h hPk
    have hsub : Finset.range (k + 1) ⊆ (Finset.range L).filter P := by
      intro x hx
      simp only [Finset.mem_range, Finset.mem_filter] at hx ⊢
      exact ⟨by omega, hP x k (by omega) hk hPk⟩
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at this
    omega
  · intro h
    have hsub : (Finset.range L).filter P ⊆ Finset.range k := by
      intro x hx
      simp only [Finset.mem_range, Finset.mem_filter] at hx ⊢
      by_contra hxk
      exact h (hP k x (by omega) hx.1 hx.2)
    simpa using Finset.card_le_card hsub

theorem card_filter_lt (L a : ℕ) :
    ((Finset.range L).filter (fun x => x < a)).card = min L a := by
  have : (Finset.range L).filter (fun x => x < a) = Finset.range (min L a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

/-! ## Padded row lengths -/

/-- The row lengths of a Young diagram, padded to `N` rows. -/
def rowsOf (N : ℕ) (μ : YoungDiagram) : Part := (List.range N).map μ.rowLen

theorem length_rowsOf (N : ℕ) (μ : YoungDiagram) : (rowsOf N μ).length = N := by
  simp [rowsOf]

theorem getD_rowsOf (N : ℕ) (μ : YoungDiagram) (r : ℕ) :
    (rowsOf N μ).getD r 0 = if r < N then μ.rowLen r else 0 := by
  simp only [rowsOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · simp [*]
  · simp [*]

/-! ## From chains to tableaux and back -/

/-- A Young diagram with at most `N` rows. -/
def RowsLE (N : ℕ) (μ : YoungDiagram) : Prop := ∀ r, N ≤ r → μ.rowLen r = 0

section Bridge

variable {N m : ℕ} {μ : YoungDiagram}

theorem mem_iff_of_rowsLE (hμ : RowsLE N μ) {r col : ℕ} :
    (r, col) ∈ μ ↔ r < N ∧ col < μ.rowLen r := by
  rw [YoungDiagram.mem_iff_lt_rowLen]
  constructor
  · intro h
    refine ⟨?_, h⟩
    by_contra hr
    rw [hμ r (by omega)] at h
    omega
  · exact fun h => h.2

theorem getD_shape (hμ : RowsLE N μ) (T : Tab N m) (hT : T.shape = rowsOf N μ) (r : ℕ) :
    (T.1 m).getD r 0 = μ.rowLen r := by
  have : T.1 m = rowsOf N μ := hT
  rw [this, getD_rowsOf]
  split
  · rfl
  · rw [hμ r (by omega)]

/-- The entry of the box `(r, col)` read from a chain: the number of steps `j < m` after which
row `r` does not yet reach past column `col`, that is, the step at which the box is added. -/
def toEntry (c : ℕ → Part) (m r col : ℕ) : ℕ :=
  ((Finset.range m).filter (fun j => (c (j + 1)).getD r 0 ≤ col)).card

theorem toEntry_lt_iff {c : ℕ → Part} (h : IsHChain N m c) {r col j : ℕ} (hj : j ≤ m) :
    toEntry c m r col < j ↔ col < (c j).getD r 0 := by
  cases j with
  | zero =>
    rw [chain_zero h]
    simp
  | succ j =>
    have hP : ∀ x y, x ≤ y → y < m → (c (y + 1)).getD r 0 ≤ col →
        (c (x + 1)).getD r 0 ≤ col :=
      fun x y hxy hy hPy => le_trans (chain_mono h r (by omega) (by omega)) hPy
    have := card_filter_le_iff (P := fun j' => (c (j' + 1)).getD r 0 ≤ col) hP
      (show j < m by omega)
    unfold toEntry
    rw [Nat.lt_succ_iff, this, not_le]

theorem toEntry_lt_succ_row {c : ℕ → Part} (h : IsHChain N m c) {r col : ℕ}
    (hcol : col < (c m).getD (r + 1) 0) : toEntry c m r col < toEntry c m (r + 1) col := by
  have hk := (toEntry_lt_iff h (Nat.le_refl m)).2 hcol
  have h1 := (toEntry_lt_iff h (r := r + 1) (col := col) (j := toEntry c m (r + 1) col + 1)
    (by omega)).1 (by omega)
  have h2 := chain_strip h r hk
  exact (toEntry_lt_iff h (j := toEntry c m (r + 1) col) (Nat.le_of_lt hk)).2 (by omega)

/-- The tableau of a chain: the box `(r, col)` holds the step at which it is added. -/
def toSSYT (hμ : RowsLE N μ) (T : Tab N m) (hT : T.shape = rowsOf N μ) :
    SemistandardYoungTableau μ where
  entry r col := if (r, col) ∈ μ then toEntry T.1 m r col else 0
  row_weak' := by
    intro r j1 j2 hj hcell
    rw [if_pos hcell, if_pos (μ.up_left_mem (Nat.le_refl _) hj.le hcell)]
    apply Finset.card_le_card
    intro j
    simp only [Finset.mem_filter]
    exact fun ⟨a, b⟩ => ⟨a, by omega⟩
  col_strict' := by
    intro r1 r2 col hr hcell
    rw [if_pos hcell, if_pos (μ.up_left_mem hr.le (Nat.le_refl _) hcell)]
    induction r2, hr using Nat.le_induction with
    | base =>
      apply toEntry_lt_succ_row T.2.1
      rw [getD_shape hμ T hT]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hcell
    | succ r2 hr2 ih =>
      have hcell' : (r2, col) ∈ μ := μ.up_left_mem (by omega) (Nat.le_refl _) hcell
      refine lt_trans (ih hcell') (toEntry_lt_succ_row T.2.1 ?_)
      rw [getD_shape hμ T hT]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hcell
  zeros' := by
    intro r col h
    exact if_neg h

theorem toSSYT_lt (hμ : RowsLE N μ) (T : Tab N m) (hT : T.shape = rowsOf N μ) (r col : ℕ)
    (hc : (r, col) ∈ μ) : toSSYT hμ T hT r col < m := by
  show (if (r, col) ∈ μ then toEntry T.1 m r col else 0) < m
  rw [if_pos hc, toEntry_lt_iff T.2.1 (Nat.le_refl m), getD_shape hμ T hT]
  exact YoungDiagram.mem_iff_lt_rowLen.mp hc

/-- The number of boxes of row `r` holding an entry `< j`. -/
def rowCount (T : SemistandardYoungTableau μ) (j r : ℕ) : ℕ :=
  ((Finset.range (μ.rowLen r)).filter (fun col => T r col < j)).card

/-- The chain of a tableau: `j ↦` the shape of the entries `< j`, padded to `N` rows. -/
def ofChain (N : ℕ) (T : SemistandardYoungTableau μ) : ℕ → Part :=
  fun j => (List.range N).map (rowCount T j)

theorem length_ofChain (T : SemistandardYoungTableau μ) (j : ℕ) :
    (ofChain N T j).length = N := by
  simp [ofChain]

theorem getD_ofChain (T : SemistandardYoungTableau μ) (j r : ℕ) :
    (ofChain N T j).getD r 0 = if r < N then rowCount T j r else 0 := by
  simp only [ofChain, List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · simp [*]
  · simp [*]

theorem rowCount_zero (T : SemistandardYoungTableau μ) (r : ℕ) : rowCount T 0 r = 0 := by
  simp [rowCount]

theorem rowCount_of_lt (T : SemistandardYoungTableau μ) (hT : ∀ i j, (i, j) ∈ μ → T i j < m)
    {j : ℕ} (hj : m ≤ j) (r : ℕ) : rowCount T j r = μ.rowLen r := by
  unfold rowCount
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro col hcol
  have := hT r col (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hcol))
  omega

theorem isHChain_ofChain (T : SemistandardYoungTableau μ) (m : ℕ) :
    IsHChain N m (ofChain N T) := by
  refine ⟨list_ext_getD (by simp [length_ofChain, zeros]) (fun r => ?_), fun j _ => ?_⟩
  · rw [getD_ofChain, rowCount_zero]
    simp [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  · rw [hstrip_iff]
    refine ⟨by simp [length_ofChain], fun r => ⟨?_, ?_⟩⟩
    · rw [getD_ofChain, getD_ofChain]
      split
      · apply Finset.card_le_card
        intro col
        simp only [Finset.mem_filter]
        exact fun ⟨a, b⟩ => ⟨a, by omega⟩
      · exact Nat.le_refl _
    · rw [getD_ofChain, getD_ofChain]
      split
      · rw [if_pos (by omega)]
        apply Finset.card_le_card
        intro col
        simp only [Finset.mem_filter, Finset.mem_range]
        intro ⟨hc, hT⟩
        have hcell : (r + 1, col) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hc
        have := T.col_strict (show r < r + 1 by omega) hcell
        exact ⟨YoungDiagram.mem_iff_lt_rowLen.mp (μ.up_left_mem (by omega) (Nat.le_refl _) hcell),
          by omega⟩
      · exact Nat.zero_le _

/-- The chain of a tableau with entries `< m`, as an element of `Tab N m`. -/
def ofSSYT (T : SemistandardYoungTableau μ)
    (hT : ∀ i j, (i, j) ∈ μ → T i j < m) : {T : Tab N m // T.shape = rowsOf N μ} :=
  ⟨Tab.mk' (ofChain N T) (isHChain_ofChain T m), by
    show freeze m (ofChain N T) m = rowsOf N μ
    simp only [freeze, Nat.min_self]
    refine list_ext_getD (by rw [length_ofChain, length_rowsOf]) (fun r => ?_)
    rw [getD_ofChain, getD_rowsOf, rowCount_of_lt T hT (Nat.le_refl m)]⟩

/-- **Chains of horizontal strips are semistandard tableaux**: for a Young diagram `μ` with at
most `N` rows, tableaux of shape `μ` with entries `< m` in the sense of `Tab N m` are in bijection
with Mathlib's `SemistandardYoungTableau μ` with entries `< m`. -/
def tabEquiv (hμ : RowsLE N μ) : {T : Tab N m // T.shape = rowsOf N μ} ≃
    {T : SemistandardYoungTableau μ // ∀ i j, (i, j) ∈ μ → T i j < m} where
  toFun T := ⟨toSSYT hμ T.1 T.2, toSSYT_lt hμ T.1 T.2⟩
  invFun T := ofSSYT T.1 T.2
  left_inv := by
    rintro ⟨T, hT⟩
    apply Subtype.ext
    apply Tab.ext'
    intro j hj
    show freeze m (ofChain N (toSSYT hμ T hT)) j = T.1 j
    simp only [freeze, Nat.min_eq_left hj]
    refine list_ext_getD (by rw [length_ofChain, chain_length T.2.1 j hj]) (fun r => ?_)
    rw [getD_ofChain]
    split
    · unfold rowCount
      have : (Finset.range (μ.rowLen r)).filter (fun col => toSSYT hμ T hT r col < j)
          = (Finset.range (μ.rowLen r)).filter (fun col => col < (T.1 j).getD r 0) := by
        apply Finset.filter_congr
        intro col hcol
        have hc : (r, col) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hcol)
        show (if (r, col) ∈ μ then toEntry T.1 m r col else 0) < j ↔ _
        rw [if_pos hc, toEntry_lt_iff T.2.1 hj]
      rw [this, card_filter_lt]
      have := chain_mono T.2.1 r hj (Nat.le_refl m)
      rw [getD_shape hμ T hT] at this
      omega
    · have hl := chain_length T.2.1 j hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  right_inv := by
    rintro ⟨T, hT⟩
    apply Subtype.ext
    ext r col
    show (if (r, col) ∈ μ then toEntry (freeze m (ofChain N T)) m r col else 0) = T r col
    split
    · rename_i hc
      have hr := (mem_iff_of_rowsLE hμ).1 hc
      unfold toEntry
      have : (Finset.range m).filter (fun j => (freeze m (ofChain N T) (j + 1)).getD r 0 ≤ col)
          = (Finset.range m).filter (fun j => j < T r col) := by
        apply Finset.filter_congr
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simp only [freeze, Nat.min_eq_left (show j + 1 ≤ m by omega)]
        rw [getD_ofChain, if_pos hr.1]
        unfold rowCount
        have hP : ∀ x y, x ≤ y → y < μ.rowLen r → T r y < j + 1 → T r x < j + 1 :=
          fun x y hxy hy h => lt_of_le_of_lt (T.row_weak_of_le hxy
            (YoungDiagram.mem_iff_lt_rowLen.mpr hy)) h
        rw [card_filter_le_iff hP hr.2]
        omega
      rw [this, card_filter_lt]
      have := hT r col hc
      omega
    · rename_i hc
      exact (T.zeros hc).symm

/-! ## Weights -/

/-- The weight of a semistandard tableau: `Σ_{(i, j) ∈ μ} x_{T i j}`. -/
noncomputable def ssytWt {ι : Type*} (x : ℕ → ι) (T : SemistandardYoungTableau μ) : ι →₀ ℕ :=
  ∑ c ∈ μ.cells, Finsupp.single (x (T c.1 c.2)) 1

theorem size_map_range (N : ℕ) (f : ℕ → ℕ) :
    size ((List.range N).map f) = ∑ r ∈ Finset.range N, f r := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, Finset.sum_range_succ, ← ih]
    simp [size, List.sum_append]

theorem rowCount_succ (T : SemistandardYoungTableau μ) (j r : ℕ) :
    rowCount T (j + 1) r
      = rowCount T j r + ∑ col ∈ Finset.range (μ.rowLen r), if T r col = j then 1 else 0 := by
  unfold rowCount
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun col _ => ?_)
  split_ifs <;> omega

theorem sum_cells (hμ : RowsLE N μ) {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M) :
    ∑ c ∈ μ.cells, f c = ∑ r ∈ Finset.range N, ∑ col ∈ Finset.range (μ.rowLen r), f (r, col) :=
  Finset.sum_finset_product _ _ _ (fun ⟨r, col⟩ => by
    rw [YoungDiagram.mem_cells, mem_iff_of_rowsLE hμ, Finset.mem_range, Finset.mem_range])

/-- **The equivalence preserves weights.** -/
theorem wt_ofSSYT {ι : Type*} (x : ℕ → ι) (hμ : RowsLE N μ) (T : SemistandardYoungTableau μ)
    (hT : ∀ i j, (i, j) ∈ μ → T i j < m) : (ofSSYT (N := N) T hT).1.wt x = ssytWt x T := by
  have key : ∀ j ∈ Finset.range m,
      (size ((ofSSYT (N := N) T hT).1.1 (j + 1)) - size ((ofSSYT (N := N) T hT).1.1 j))
        • Finsupp.single (x j) 1
      = ∑ r ∈ Finset.range N, ∑ col ∈ Finset.range (μ.rowLen r),
          (if T r col = j then Finsupp.single (x j) 1 else 0) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    show (size (freeze m (ofChain N T) (j + 1)) - size (freeze m (ofChain N T) j)) • _ = _
    simp only [freeze, Nat.min_eq_left (show j + 1 ≤ m from hj'), Nat.min_eq_left hj'.le,
      ofChain, size_map_range, rowCount_succ, Finset.sum_add_distrib, Nat.add_sub_cancel_left,
      Finset.sum_smul]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun col _ => ?_))
    split_ifs <;> simp
  rw [Tab.wt, Finset.sum_congr rfl key, Finset.sum_comm, ssytWt, sum_cells hμ]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun col hcol => ?_)
  rw [Finset.sum_ite_eq, if_pos]
  exact Finset.mem_range.mpr
    (hT r col (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hcol)))

/-- **The Schur polynomial on Mathlib's tableaux**: `s_μ(x₀, …, x_{m−1})` as the total weight of
the semistandard Young tableaux of shape `μ` with entries `< m`. -/
noncomputable def schurSSYT {ι : Type*} (R : Type*) [CommSemiring R] [TopologicalSpace R]
    (x : ℕ → ι) (m : ℕ) (μ : YoungDiagram) : MvPowerSeries ι R :=
  ∑' T : {T : SemistandardYoungTableau μ // ∀ i j, (i, j) ∈ μ → T i j < m}, mono (ssytWt x T.1)

theorem schur_eq_schurSSYT {ι R : Type*} [CommSemiring R] [TopologicalSpace R] (x : ℕ → ι)
    (hμ : RowsLE N μ) : schur R x N m (rowsOf N μ) = schurSSYT R x m μ := by
  rw [schur, schurSSYT, ← (tabEquiv (m := m) hμ).symm.tsum_eq]
  refine tsum_congr (fun T => ?_)
  rw [← wt_ofSSYT x hμ T.1 T.2]
  rfl

end Bridge

/-! ## The Cauchy identity over Young diagrams -/

/-- Every shape of a chain of horizontal strips from the empty shape is a partition. -/
theorem chain_partition {N m : ℕ} {c : ℕ → Part} (h : IsHChain N m c) :
    ∀ k, k ≤ m → RMT.RSK.GrowthSuper.Partition (c k)
  | 0, _ => by rw [h.1]; exact RMT.RSK.GrowthSuper.partition_zeros N
  | k + 1, hk => RMT.RSK.GrowthSuper.Strip.partition (p := false)
      (chain_partition h k (by omega)) (h.2 k hk)

theorem partition_getD_succ : ∀ {l : Part}, RMT.RSK.GrowthSuper.Partition l →
    ∀ k, l.getD (k + 1) 0 ≤ l.getD k 0
  | [], _, _ => by simp
  | [_], _, k => by cases k <;> simp
  | a :: b :: l, h, k => by
    cases k with
    | zero => exact h.1
    | succ k => simpa using partition_getD_succ h.2 k

theorem partition_sortedGE {l : Part} (h : RMT.RSK.GrowthSuper.Partition l) : l.SortedGE := by
  intro i j hij
  have hmono : ∀ d k, l.getD (k + d) 0 ≤ l.getD k 0 := by
    intro d
    induction d with
    | zero => intro k; exact Nat.le_refl _
    | succ d ih => intro k; exact le_trans (partition_getD_succ h (k + d)) (ih k)
  have := hmono (j - i) i
  rw [show i.1 + (j.1 - i.1) = j.1 by have : i.1 ≤ j.1 := hij; omega] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2,
    List.getElem?_eq_getElem j.2] using this

theorem rowLen_ofRowLens' (w : List ℕ) (hw : w.SortedGE) (r : ℕ) :
    (YoungDiagram.ofRowLens w hw).rowLen r = w.getD r 0 := by
  apply eq_of_forall_lt_iff
  intro c
  rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_ofRowLens]
  by_cases hr : r < w.length
  · simp [hr, List.getD_eq_getElem?_getD]
  · simp [hr, List.getD_eq_getElem?_getD]

theorem ofRowLens_rowsLE {N : ℕ} (w : List ℕ) (hw : w.SortedGE) (hN : w.length = N) :
    RowsLE N (YoungDiagram.ofRowLens w hw) := by
  intro r hr
  rw [rowLen_ofRowLens', List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem rowsOf_ofRowLens {N : ℕ} (w : List ℕ) (hw : w.SortedGE) (hN : w.length = N) :
    rowsOf N (YoungDiagram.ofRowLens w hw) = w := by
  refine list_ext_getD (by rw [length_rowsOf, hN]) (fun r => ?_)
  rw [getD_rowsOf, rowLen_ofRowLens']
  split
  · rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem rowsOf_injective {N : ℕ} {μ ν : YoungDiagram} (hμ : RowsLE N μ) (hν : RowsLE N ν)
    (h : rowsOf N μ = rowsOf N ν) : μ = ν := by
  have hr : ∀ r, μ.rowLen r = ν.rowLen r := by
    intro r
    by_cases hrN : r < N
    · have := congrArg (fun l => l.getD r 0) h
      simp only [getD_rowsOf, if_pos hrN] at this
      exact this
    · rw [hμ r (by omega), hν r (by omega)]
  apply YoungDiagram.ext
  ext ⟨r, c⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen, hr]

/-- A tableau with entries `< m` has at most `m` rows. -/
theorem rowsLE_of_ssyt {m : ℕ} {μ : YoungDiagram} (T : SemistandardYoungTableau μ)
    (hT : ∀ i j, (i, j) ∈ μ → T i j < m) : RowsLE m μ := by
  intro r hr
  by_contra h0
  have hcell : (r, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h0)
  have key : ∀ k, k ≤ r → k ≤ T k 0 := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have := T.col_strict (show k < k + 1 by omega) (μ.up_left_mem hk (Nat.le_refl _) hcell)
      have := ih (by omega)
      omega
  have := key r (Nat.le_refl _)
  have := hT r 0 hcell
  omega

section Cauchy

variable {ι R : Type*} [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
  [T3Space R] {m n : ℕ}

/-- **The Cauchy identity over Young diagrams**, with Mathlib's semistandard Young tableaux:

  `∑' μ, s_μ(x₀, …, x_{m−1}) s_μ(y₀, …, y_{n−1}) = ∑' A, ∏_{i<n, j<m} (x_j y_i) ^ (A i j)`

in `MvPowerSeries ι R` with the product topology, the sum on the left over all Young diagrams,
`s_μ` the total weight of the tableaux of shape `μ` with entries `< m` (resp. `< n`). -/
theorem cauchy_ssyt (x y : ℕ → ι) :
    ∑' μ : YoungDiagram, schurSSYT R x m μ * schurSSYT R y n μ
      = ∑' A : Fin n → Fin m → ℕ, (mono (matWt x y A) : MvPowerSeries ι R) := by
  rw [← cauchy (N := m) x y (Nat.le_refl m)]
  -- the Mathlib side is supported on diagrams with at most `m` rows
  have hsupp : Function.support (fun μ : YoungDiagram => schurSSYT R x m μ * schurSSYT R y n μ)
      ⊆ {μ | RowsLE m μ} := by
    intro μ hμ
    by_contra hle
    apply hμ
    have : IsEmpty {T : SemistandardYoungTableau μ // ∀ i j, (i, j) ∈ μ → T i j < m} :=
      ⟨fun T => hle (rowsLE_of_ssyt T.1 T.2)⟩
    show schurSSYT R x m μ * _ = 0
    rw [schurSSYT, tsum_empty, zero_mul]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  -- transport along `μ ↦ rowsOf m μ`
  let g : {μ : YoungDiagram // RowsLE m μ} → Part := fun μ => rowsOf m μ.1
  have hg : Function.Injective g := fun μ ν h => Subtype.ext (rowsOf_injective μ.2 ν.2 h)
  have hrange : Function.support (fun lam : Part => schur R x m m lam * schur R y m n lam)
      ⊆ Set.range g := by
    intro lam hlam
    by_contra hnot
    apply hlam
    have : IsEmpty {T : Tab m m // T.shape = lam} := by
      refine ⟨fun T => hnot ?_⟩
      have hp := chain_partition T.1.2.1 m (Nat.le_refl m)
      have hsh : T.1.1 m = lam := T.2
      have hlen : lam.length = m := by rw [← hsh]; exact chain_length T.1.2.1 m (Nat.le_refl m)
      rw [hsh] at hp
      exact ⟨⟨YoungDiagram.ofRowLens lam (partition_sortedGE hp),
        ofRowLens_rowsLE lam (partition_sortedGE hp) hlen⟩,
        rowsOf_ofRowLens lam (partition_sortedGE hp) hlen⟩
    show schur R x m m lam * _ = 0
    rw [schur, tsum_empty, zero_mul]
  rw [← hg.tsum_eq hrange]
  refine tsum_congr (fun μ => ?_)
  show schurSSYT R x m μ.1 * schurSSYT R y n μ.1
    = schur R x m m (rowsOf m μ.1) * schur R y m n (rowsOf m μ.1)
  rw [schur_eq_schurSSYT x μ.2, schur_eq_schurSSYT y μ.2]

end Cauchy

/-- **The Cauchy identity over Young diagrams, product form**:

  `(∏_{i<n, j<m} (1 − x_j y_i)) · ∑' μ, s_μ(x₀, …, x_{m−1}) s_μ(y₀, …, y_{n−1}) = 1`

in `MvPowerSeries ι R` with the product topology, `s_μ` the total weight of Mathlib's
semistandard Young tableaux of shape `μ`. -/
theorem cauchy_prod_ssyt {ι R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T3Space R] {m n : ℕ} (x y : ℕ → ι) :
    (∏ i : Fin n, ∏ j : Fin m, (1 - X (x j) * X (y i) : MvPowerSeries ι R))
      * ∑' μ : YoungDiagram, schurSSYT R x m μ * schurSSYT R y n μ = 1 := by
  rw [cauchy_ssyt, ← cauchy (N := m) x y (Nat.le_refl m)]
  exact cauchy_prod x y (Nat.le_refl m)

end RMT.Symmetric
