import RMTlib.RSK.Fomin
import RMTlib.Growth.Matrix

/-!
# RSK of a two-line array, through standardization

`RMT.Growth.rskTwoLine` runs the growth diagram on the standardized word of the bottom line and
then puts the original entries back. This file proves that the result is the bumping RSK of the
bottom line, ties included, with the recording tableau labelled by the top line
(`rskTwoLine_eq`).

The key step (`ins_map`) is that row insertion commutes with a weakly increasing relabelling
`f`, provided the inserted value is the largest of its `f`-class so far and, in the tableau,
equal labels lower down carry smaller values (`StdT`). Standardization breaks ties from left
to right, so both conditions hold along the word.

Mathlib-free.
-/

namespace RMT.RSK.Fomin

open RMT.RSK RMT.RSK.Nested RMT.Growth

/-- Equal labels in lower rows carry smaller values. -/
def StdT (f : Nat → Nat) : Tab → Prop
  | [] => True
  | r :: rs => (∀ y ∈ r, ∀ z ∈ rs.flatten, f y = f z → z < y) ∧ StdT f rs

theorem rowIns_map {f : Nat → Nat} (hf : ∀ a b, a ≤ b → f a ≤ f b) (x : Nat) :
    ∀ (r : Row), (∀ z ∈ r, f z = f x → z < x) →
      rowIns (f x) (r.map f) = ((rowIns x r).1.map f, (rowIns x r).2.map f)
  | [], _ => by simp [rowIns]
  | z :: zs, h => by
    by_cases hxz : x < z
    · have h1 := hf x z (Nat.le_of_lt hxz)
      have h2 : f z ≠ f x := fun e => by have := h z (by simp) e; omega
      have : f x < f z := by omega
      simp [rowIns, hxz, this]
    · have : ¬ f x < f z := by have := hf z x (by omega); omega
      have ih := rowIns_map hf x zs (fun u hu => h u (by simp [hu]))
      simp [rowIns, hxz, this, ih]

theorem rowIns_bump_le (x : Nat) : ∀ (r : Row), Sorted r → ∀ r' y, rowIns x r = (r', some y) →
    ∀ u ∈ r, x < u → y ≤ u
  | [], _, _, _, h, _, _, _ => by simp [rowIns] at h
  | z :: zs, hs, r', y, h, u, hu, hxu => by
    have hz := (List.pairwise_cons.mp hs).1
    by_cases hxz : x < z
    · simp [rowIns, hxz] at h; obtain ⟨_, rfl⟩ := h
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Nat.le_refl _
      · exact hz u hu
    · simp only [rowIns, hxz, ↓reduceIte, Prod.mk.injEq] at h
      rcases List.mem_cons.mp hu with rfl | hu
      · omega
      · exact rowIns_bump_le x zs (List.pairwise_cons.mp hs).2 _ y (Prod.ext rfl h.2) u hu hxu

/-- **Insertion commutes with relabelling.** -/
theorem ins_map {f : Nat → Nat} (hf : ∀ a b, a ≤ b → f a ≤ f b) : ∀ (t : Tab) (x : Nat),
    Good t → t.flatten.Nodup → x ∉ t.flatten → (∀ z ∈ t.flatten, f z = f x → z < x) → StdT f t →
    ins (f x) (t.map (·.map f)) = ((ins x t).1.map (·.map f), (ins x t).2) ∧ StdT f (ins x t).1
  | [], x, _, _, _, _, _ => by simp [ins, StdT]
  | r :: rs, x, hg, hnd, hx, hcl, hstd => by
    have hr := hg r (by simp)
    have hnd' : r.Nodup ∧ rs.flatten.Nodup ∧ ∀ a ∈ r, a ∉ rs.flatten := by
      simp only [List.flatten_cons, List.nodup_append] at hnd
      exact ⟨hnd.1, hnd.2.1, fun a ha hb => hnd.2.2 a ha a hb rfl⟩
    have hxr : x ∉ r := fun h => hx (by simp [List.flatten_cons, h])
    have hxrs : x ∉ rs.flatten := fun h => hx (by simp only [List.flatten_cons]; exact List.mem_append_right _ h)
    have hrm := rowIns_map hf x r (fun z hz => hcl z (by simp [List.flatten_cons, hz]))
    have hp := rowIns_perm x r
    cases hrow : rowIns x r with
    | mk r' b =>
      rw [hrow] at hrm hp
      cases b with
      | none =>
        rw [ins_cons_none hrow]
        simp only [Option.map_none] at hrm
        simp only [List.map_cons]
        rw [ins_cons_none hrm]
        refine ⟨rfl, ?_, hstd.2⟩
        intro u hu z hz e
        simp only [Option.toList_none, List.append_nil] at hp
        rcases List.mem_cons.mp (hp.mem_iff.mp hu) with rfl | hu
        · exact hcl z (by simp only [List.flatten_cons]; exact List.mem_append_right _ hz) e.symm
        · exact hstd.1 u hu z hz e
      | some y =>
        rw [ins_cons_some hrow]
        simp only [Option.map_some] at hrm
        simp only [List.map_cons]
        rw [ins_cons_some hrm]
        simp only [Option.toList_some] at hp
        have hyr : y ∈ r := rowIns_mem_bump x r y (by simp [hrow])
        have hxy : x < y := rowIns_bump_gt x r y (by simp [hrow])
        have hfxy : f x ≠ f y := fun e => by
          have := hcl y (by simp [List.flatten_cons, hyr]) e.symm; omega
        obtain ⟨ih1, ih2⟩ := ins_map hf rs y hg.tail hnd'.2.1 (hnd'.2.2 y hyr)
          (fun z hz e => hstd.1 y hyr z hz e.symm) hstd.2
        rw [ih1]
        refine ⟨rfl, ?_, ih2⟩
        -- the new top row against the new rows below
        have hyr' : y ∉ r' := by
          have hn : (x :: r).Nodup := List.nodup_cons.mpr ⟨hxr, hnd'.1⟩
          have hn' := hp.symm.nodup_iff.mp hn
          simp only [List.nodup_append] at hn'
          exact fun h => hn'.2.2 y h y (by simp) rfl
        intro u hu z hz e
        have hz' := (ins_perm y rs).mem_iff.mp hz
        have hu' := hp.mem_iff.mp (List.mem_append_left _ hu)
        rcases List.mem_cons.mp hu' with rfl | hu'
        · rcases List.mem_cons.mp hz' with rfl | hz'
          · exact absurd e hfxy
          · exact hcl z (by simp only [List.flatten_cons]; exact List.mem_append_right _ hz') e.symm
        · rcases List.mem_cons.mp hz' with rfl | hz'
          · -- `u` and the bumped `z` have the same label: `u` lies after the bump
            have hne : u ≠ z := fun h => hyr' (h ▸ hu)
            refine Nat.lt_of_le_of_ne ?_ (Ne.symm hne)
            refine Nat.le_of_not_lt fun hlt => ?_
            have hux : u ≤ x := Nat.le_of_not_lt fun hxu =>
              absurd (rowIns_bump_le x r hr.1 r' z hrow u hu' hxu) (by omega)
            have := hf u x hux; have := hf x z (Nat.le_of_lt hxy)
            exact hfxy (by omega)
          · exact hstd.1 u hu' z hz' e

/-! ### Standardization -/

/-- The comparison used by `standardize`: lexicographic on (value, position). -/
def stCmp (p q : Nat × Nat) : Bool := p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2)

/-- The (value, position) pairs of `bs`, sorted lexicographically. -/
def stSorted (bs : List Nat) : List (Nat × Nat) :=
  (bs.zip (List.range bs.length)).mergeSort stCmp

/-- The position of `(bs[i], i)` in `stSorted bs`. -/
def stPos (bs : List Nat) (i : Nat) : Nat := ((stSorted bs).findIdx? (·.2 == i)).getD 0

theorem standardize_eq (bs : List Nat) :
    standardize bs = (List.range bs.length).map (stPos bs) := rfl

section
variable (bs : List Nat)

theorem stSorted_pairwise : (stSorted bs).Pairwise (fun p q => stCmp p q = true) :=
  List.pairwise_mergeSort (fun a b c => by simp [stCmp]; omega) (fun a b => by simp [stCmp]; omega) _

theorem stSorted_perm : (stSorted bs).Perm (bs.zip (List.range bs.length)) :=
  List.mergeSort_perm _ _

theorem length_stSorted : (stSorted bs).length = bs.length := by simp [stSorted]

theorem mem_zip_range {p : Nat × Nat} (h : p ∈ bs.zip (List.range bs.length)) :
    p.2 < bs.length ∧ p.1 = bs.getD p.2 0 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  simp at hk
  simp [List.getElem_zip, hk]

theorem stSorted_nodup : (stSorted bs).Nodup := by
  refine (stSorted_perm bs).nodup_iff.mpr ?_
  have h : ((bs.zip (List.range bs.length)).map Prod.snd).Nodup := by
    rw [List.map_snd_zip (by simp)]; exact List.nodup_range
  exact (List.pairwise_map.mp h).imp fun h e => h (congrArg Prod.snd e)

theorem mem_stSorted {p : Nat × Nat} (h : p ∈ stSorted bs) :
    p.2 < bs.length ∧ p.1 = bs.getD p.2 0 :=
  mem_zip_range bs ((stSorted_perm bs).mem_iff.mp h)

theorem stPos_spec {i : Nat} (hi : i < bs.length) :
    ∃ h : stPos bs i < (stSorted bs).length, (stSorted bs)[stPos bs i] = (bs.getD i 0, i) := by
  have hmem : (bs.getD i 0, i) ∈ stSorted bs := by
    refine (stSorted_perm bs).mem_iff.mpr ?_
    rw [List.mem_iff_getElem]
    exact ⟨i, by simpa using hi, by simp [List.getElem_zip, hi]⟩
  have hex : ∃ x, x ∈ stSorted bs ∧ (x.2 == i) = true := ⟨_, hmem, by simp⟩
  have e := List.findIdx?_eq_some_of_exists hex
  obtain ⟨hk, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp e
  have hpos : stPos bs i = (stSorted bs).findIdx (·.2 == i) := by simp [stPos, e]
  refine ⟨hpos ▸ hk, ?_⟩
  have h2 : ((stSorted bs)[stPos bs i]'(hpos ▸ hk)).2 = i := by
    simp only [hpos]; simpa using hp
  have := mem_stSorted bs (List.getElem_mem (hpos ▸ hk))
  rw [h2] at this
  exact Prod.ext this.2 h2

theorem stPos_lt {i : Nat} (hi : i < bs.length) : stPos bs i < bs.length := by
  obtain ⟨h, -⟩ := stPos_spec bs hi; simpa [length_stSorted] using h

theorem stPos_eq {i k : Nat} (hk : k < (stSorted bs).length) (h : ((stSorted bs)[k]).2 = i) :
    stPos bs i = k := by
  have hi : i < bs.length := h ▸ (mem_stSorted bs (List.getElem_mem hk)).1
  obtain ⟨h1, e⟩ := stPos_spec bs hi
  have e' : (stSorted bs)[k] = (bs.getD i 0, i) := by
    have := mem_stSorted bs (List.getElem_mem hk); rw [h] at this; exact Prod.ext this.2 h
  exact (List.Nodup.getElem_inj (stSorted_nodup bs)).mp (e.trans e'.symm)

/-- The standardized word is a permutation of `0, …, n-1`. -/
theorem standardize_perm : (standardize bs).Perm (List.range (standardize bs).length) := by
  have hlen : (standardize bs).length = bs.length := by simp [standardize_eq]
  rw [hlen]
  apply (List.perm_ext_iff_of_nodup _ List.nodup_range).mpr
  · intro v
    simp only [standardize_eq, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact stPos_lt bs hi
    · intro hv
      have hv' : v < (stSorted bs).length := by simpa [length_stSorted] using hv
      exact ⟨_, (mem_stSorted bs (List.getElem_mem hv')).1, stPos_eq bs hv' rfl⟩
  · rw [standardize_eq]
    refine List.pairwise_map.mpr (List.nodup_range.imp_of_mem ?_)
    intro i j hi hj hij e
    simp only [List.mem_range] at hi hj
    obtain ⟨h1, e1⟩ := stPos_spec bs hi
    obtain ⟨h2, e2⟩ := stPos_spec bs hj
    have : (stSorted bs)[stPos bs i] = (stSorted bs)[stPos bs j] := by simp only [e]
    rw [e1, e2] at this; exact hij (Prod.ext_iff.mp this).2

theorem getD_standardize {i : Nat} (hi : i < bs.length) :
    (standardize bs).getD i 0 = stPos bs i := by
  simp [standardize_eq, hi]

/-- The sorted bottom line is the first component of `stSorted`. -/
theorem mergeSort_eq_map_fst :
    bs.mergeSort (fun a b => decide (a ≤ b)) = (stSorted bs).map Prod.fst := by
  symm
  apply List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true)
  · intro a b _ _ h1 h2; simp at h1 h2; omega
  · rw [List.pairwise_map]
    exact (stSorted_pairwise bs).imp fun {p q} h => by simp [stCmp] at h ⊢; omega
  · exact List.pairwise_mergeSort (fun a b c => by simp; omega) (fun a b => by simp; omega) _
  · refine ((stSorted_perm bs).map Prod.fst).trans ?_
    rw [List.map_fst_zip (by simp)]
    exact (List.mergeSort_perm _ _).symm

/-- Putting the values back: position `stPos i` of the sorted bottom line holds `bs[i]`. -/
theorem getD_mergeSort_stPos {i : Nat} (hi : i < bs.length) :
    (bs.mergeSort (fun a b => decide (a ≤ b))).getD (stPos bs i) 0 = bs.getD i 0 := by
  obtain ⟨h, e⟩ := stPos_spec bs hi
  rw [mergeSort_eq_map_fst]
  simp [h, e]

/-- Ties are broken from left to right. -/
theorem stPos_lt_of_eq {i k : Nat} (hik : i < k) (hk : k < bs.length)
    (e : bs.getD i 0 = bs.getD k 0) : stPos bs i < stPos bs k := by
  obtain ⟨h1, e1⟩ := stPos_spec bs (by omega : i < bs.length)
  obtain ⟨h2, e2⟩ := stPos_spec bs hk
  refine Nat.lt_of_not_le fun hle => ?_
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · have : (stSorted bs)[stPos bs i] = (stSorted bs)[stPos bs k] := by simp only [heq]
    rw [e1, e2] at this; have := (Prod.ext_iff.mp this).2; simp at this; omega
  · have := List.pairwise_iff_getElem.mp (stSorted_pairwise bs) _ _ h2 h1 hlt
    rw [e1, e2, e] at this; simp [stCmp] at this; omega

end

/-! ### RSK of a two-line array -/

/-- The recording tableau of the first `i` letters of `w`, the new box at step `i` labelled
`labels[i]`. -/
def recL (labels w : List Nat) : Nat → Tab
  | 0 => []
  | i + 1 => tabAdd (recL labels w i) (ins (w.getD i 0) (insT w i)).2 (labels.getD i 0)

theorem recT_map_eq_recL (labels w : List Nat) : ∀ i,
    (recT w i).map (·.map fun j => labels.getD (j - 1) 0) = recL labels w i
  | 0 => rfl
  | i + 1 => by
    simp only [recT, recL, map_tabAdd, recT_map_eq_recL labels w i]; rfl

theorem map_congr_tab {g h : Nat → Nat} : ∀ (t : Tab), (∀ v ∈ t.flatten, g v = h v) →
    t.map (·.map g) = t.map (·.map h)
  | [], _ => rfl
  | r :: rs, hv => by
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨List.map_congr_left fun v hv' => hv v (by simp [List.flatten_cons, hv']),
      map_congr_tab rs fun v hv' => hv v (by simp only [List.flatten_cons]; exact List.mem_append_right _ hv')⟩

theorem mem_take_getD {l : List Nat} {i z : Nat} (h : z ∈ l.take i) :
    ∃ k, k < i ∧ k < l.length ∧ z = l.getD k 0 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_take] at hk
  have hk' := Nat.lt_min.mp hk
  exact ⟨k, hk'.1, hk'.2, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'.2]⟩

/-- Bumping on the bottom line is the relabelled bumping on the standardized word. -/
theorem insT_standardize (bs : List Nat) :
    let f := fun v => (bs.mergeSort (fun a b => decide (a ≤ b))).getD (min v (bs.length - 1)) 0
    ∀ i, i ≤ bs.length →
      insT bs i = (insT (standardize bs) i).map (·.map f) ∧ StdT f (insT (standardize bs) i) ∧
      recT bs i = recT (standardize bs) i := by
  intro f
  have hsl : (standardize bs).length = bs.length := by simp [standardize_eq]
  have hst := standardize_perm bs
  have hnd : (standardize bs).Nodup := hst.nodup_iff.mpr List.nodup_range
  have hsorted := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c => by simp; omega) (fun a b => by simp; omega) bs
  have hmono : ∀ a b, a ≤ b → f a ≤ f b := by
    intro a b hab
    simp only [f]
    by_cases hn : bs.length = 0
    · have : bs = [] := List.eq_nil_of_length_eq_zero hn
      subst this; simp
    · have hl : (bs.mergeSort (fun a b => decide (a ≤ b))).length = bs.length := by simp
      have h1 : min a (bs.length - 1) < bs.length := by omega
      have h2 : min b (bs.length - 1) < bs.length := by omega
      rcases Nat.eq_or_lt_of_le (show min a (bs.length - 1) ≤ min b (bs.length - 1) by omega)
        with e | hlt
      · rw [e]; exact Nat.le_refl _
      · have := List.pairwise_iff_getElem.mp hsorted _ _ (by omega) (by omega) hlt
        simp only [decide_eq_true_eq] at this
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [hl]; exact h1),
          List.getElem?_eq_getElem (by rw [hl]; exact h2)]
        exact this
  have hfx : ∀ i, i < bs.length → f (stPos bs i) = bs.getD i 0 := by
    intro i hi
    have := stPos_lt bs hi
    simp only [f, show min (stPos bs i) (bs.length - 1) = stPos bs i by omega]
    exact getD_mergeSort_stPos bs hi
  intro i
  induction i with
  | zero => intro _; exact ⟨rfl, trivial, rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    have hil : i < bs.length := by omega
    have hP := insT_perm (standardize bs) i (by omega)
    have hx : (standardize bs).getD i 0 = stPos bs i := getD_standardize bs hil
    have hndP : (insT (standardize bs) i).flatten.Nodup :=
      hP.nodup_iff.mpr ((List.take_sublist _ _).nodup hnd)
    have hxn : stPos bs i ∉ (insT (standardize bs) i).flatten := by
      intro hm
      obtain ⟨k, hk, hkl, e⟩ := mem_take_getD (hP.mem_iff.mp hm)
      rw [← hx] at e
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at e
      have := (List.Nodup.getElem_inj hnd).mp (by simpa using e.symm); omega
    have hcl : ∀ z ∈ (insT (standardize bs) i).flatten, f z = f (stPos bs i) → z < stPos bs i := by
      intro z hz e
      obtain ⟨k, hk, hkl, rfl⟩ := mem_take_getD (hP.mem_iff.mp hz)
      rw [hsl] at hkl
      rw [getD_standardize bs hkl] at e ⊢
      rw [hfx k hkl, hfx i hil] at e
      exact stPos_lt_of_eq bs hk hil e
    obtain ⟨hm1, hm2⟩ := ins_map hmono _ (stPos bs i) (insT_ssyt _ i).good hndP hxn hcl ih2
    refine ⟨?_, ?_, ?_⟩
    · simp only [insT]; rw [hx, ih1, ← hfx i hil, hm1]
    · simp only [insT]; rw [hx]; exact hm2
    · simp only [recT]; rw [ih3, hx, ih1, ← hfx i hil, hm1]

/-- **Knuth's RSK of a two-line array.** `rskTwoLine` (growth diagram of the standardized
word, entries put back) is the bumping RSK of the bottom line, inserted left to right, with
the box created at step `i` labelled by the `i`-th top entry. -/
theorem rskTwoLine_eq (pairs : TwoLine) :
    rskTwoLine pairs = (insT (pairs.map (·.2)) pairs.length,
      recL (pairs.map (·.1)) (pairs.map (·.2)) pairs.length) := by
  have hl : (pairs.map (·.2)).length = pairs.length := by simp
  have hsl : (standardize (pairs.map (·.2))).length = pairs.length := by
    simp [standardize_eq]
  have hst := standardize_perm (pairs.map (·.2))
  obtain ⟨h1, -, h3⟩ := insT_standardize (pairs.map (·.2)) pairs.length (by simp)
  simp only [rskTwoLine]
  rw [rsk_eq _ hst, hsl, h1, ← h3, ← recT_map_eq_recL]
  simp only [Prod.mk.injEq, and_true]
  rw [List.map_map, show ((fun x : Row => x.map fun v =>
      ((pairs.map (·.2)).mergeSort fun x1 x2 => decide (x1 ≤ x2)).getD (v - 1) 0) ∘
      fun x : Row => x.map (· + 1)) = fun x : Row => x.map fun v =>
      ((pairs.map (·.2)).mergeSort fun x1 x2 => decide (x1 ≤ x2)).getD v 0 from by
    funext x; simp [Function.comp]]
  apply map_congr_tab
  intro v hv
  have hv' : v < pairs.length := by
    have := allLt_insT _ hst pairs.length (by omega)
    obtain ⟨row, hrow, hvr⟩ := List.mem_flatten.mp hv
    have := this row hrow v hvr; omega
  simp [show min v (pairs.length - 1) = v by omega]

end RMT.RSK.Fomin
