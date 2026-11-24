import RMTlib.RSK.Standardize

/-!
# Inserting a whole row

Bumping a weakly increasing row `r` into a semistandard tableau `T`, one entry after another.

* `insList_row`: if `r` sits on top of `T` as a semistandard tableau, the result is `r :: T`,
  and the new boxes are at the bottoms of the columns `0, …, |r| - 1` of `T` (`colHeights`):
  each entry pushes one column of `T` down by one row.
* `rowFold_bumps_lt`: if `r` does not sit on top of the first row `s` of `T`, fewer than `|s|`
  entries of `r` bump anything out of the first row, so the first row ends up longer than `|r|`.

Mathlib-free.
-/

namespace RMT.RSK.Fomin

open RMT.RSK RMT.RSK.Nested RMT.Growth

/-- Insert a list of values one after another; also return the row of each new box. -/
def insList : Tab → List Nat → Tab × List Nat
  | t, [] => (t, [])
  | t, x :: xs => ((insList (ins x t).1 xs).1, (ins x t).2 :: (insList (ins x t).1 xs).2)

/-- Insert a list of values one after another into a single row; also return what each one
bumped out. -/
def rowFold : Row → List Nat → Row × List (Option Nat)
  | s, [] => (s, [])
  | s, x :: xs => ((rowFold (rowIns x s).1 xs).1, (rowIns x s).2 :: (rowFold (rowIns x s).1 xs).2)

/-- The height of column `j` of a shape. -/
def colH (sh : List Nat) (j : Nat) : Nat := (sh.filter (j < ·)).length

/-- The heights of the columns `0, …, L - 1` of a shape. -/
def colHeights (sh : List Nat) (L : Nat) : List Nat := (List.range L).map (colH sh)

theorem insList_append (t : Tab) : ∀ (u v : List Nat),
    insList t (u ++ v) = ((insList (insList t u).1 v).1, (insList t u).2 ++ (insList (insList t u).1 v).2)
  | [], v => by simp [insList]
  | x :: u, v => by
    simp only [List.cons_append, insList, insList_append (ins x t).1 u v, List.cons_append]

/-- The first row evolves on its own. -/
theorem insList_head : ∀ (xs : List Nat) (s : Row) (rest : Tab),
    ∃ rest', (insList (s :: rest) xs).1 = (rowFold s xs).1 :: rest'
  | [], s, rest => ⟨rest, rfl⟩
  | x :: xs, s, rest => by
    have e : ∃ rest'', (ins x (s :: rest)).1 = (rowIns x s).1 :: rest'' := by
      cases hrow : rowIns x s with
      | mk r' b => cases b with
        | none => exact ⟨rest, by rw [ins_cons_none hrow]⟩
        | some y => exact ⟨(ins y rest).1, by rw [ins_cons_some hrow]⟩
    obtain ⟨rest'', e⟩ := e
    obtain ⟨rest', e'⟩ := insList_head xs (rowIns x s).1 rest''
    exact ⟨rest', by simp only [insList, rowFold, e, e']⟩

/-! ### Counting bumps -/

/-- The number of entries that bumped something. -/
def nBumps (l : List (Option Nat)) : Nat := (l.filter Option.isSome).length

theorem rowIns_none_le (x : Nat) : ∀ (s : Row), (rowIns x s).2 = none → ∀ v ∈ s, v ≤ x
  | [], _ => by simp
  | z :: zs, h => by
    unfold rowIns at h; split at h
    · simp at h
    · rename_i hxz; intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · omega
      · exact rowIns_none_le x zs h v hv

theorem rowFold_length : ∀ (xs : List Nat) (s : Row),
    (rowFold s xs).1.length + nBumps (rowFold s xs).2 = s.length + xs.length
  | [], s => by simp [rowFold, nBumps]
  | x :: xs, s => by
    cases hb : (rowIns x s).2 with
    | none =>
      have e : rowIns x s = (s ++ [x], none) := Prod.ext (rowIns_none x s hb) hb
      have ih := rowFold_length xs (s ++ [x])
      simp only [rowFold, nBumps, e, List.filter_cons, Option.isSome_none] at ih ⊢
      simp at ih ⊢; omega
    | some y =>
      have ih := rowFold_length xs (rowIns x s).1
      have := rowIns_length_some x s y hb
      simp only [rowFold, nBumps, hb, List.filter_cons, Option.isSome_some] at ih ⊢
      simp; omega

theorem filter_gt_length_mono {a b : Nat} (h : a ≤ b) (s : Row) :
    (s.filter (b < ·)).length ≤ (s.filter (a < ·)).length := by
  induction s with
  | nil => simp
  | cons z zs ih =>
    by_cases hb : b < z
    · simp [hb, show a < z by omega]; omega
    · by_cases ha : a < z
      · simp [hb, ha]; omega
      · simp [hb, ha]; omega

/-- Inserting values `≥ x0` in increasing order bumps at most as many times as the row has
entries `> x0`. -/
theorem rowFold_bumps_le : ∀ (xs : List Nat) (s : Row) (x0 : Nat), Sorted xs → (∀ x ∈ xs, x0 ≤ x) →
    nBumps (rowFold s xs).2 ≤ (s.filter (x0 < ·)).length
  | [], s, x0, _, _ => by simp [rowFold, nBumps]
  | x :: xs, s, x0, hs, hx => by
    have hxs : ∀ y ∈ xs, x ≤ y := (List.pairwise_cons.mp hs).1
    have hmono := filter_gt_length_mono (hx x (by simp)) s
    have hp := rowIns_perm x s
    cases hb : (rowIns x s).2 with
    | none =>
      have hle := rowIns_none_le x s hb
      have e : rowIns x s = (s ++ [x], none) := Prod.ext (rowIns_none x s hb) hb
      have ih := rowFold_bumps_le xs (s ++ [x]) x (List.pairwise_cons.mp hs).2 hxs
      have h0 : ((s ++ [x]).filter (x < ·)).length = 0 := by
        simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro a ha; simp at ha ⊢; rcases ha with ha | rfl
        · exact hle a ha
        · exact Nat.le_refl _
      simp only [rowFold, nBumps, e, List.filter_cons, Option.isSome_none] at ih ⊢
      simp only [Bool.false_eq_true, ↓reduceIte]; omega
    | some y =>
      have ih := rowFold_bumps_le xs (rowIns x s).1 x (List.pairwise_cons.mp hs).2 hxs
      rw [hb] at hp
      have hxy : x < y := rowIns_bump_gt x s y hb
      have hc := (hp.filter (x < ·)).length_eq
      simp [hxy, show ¬ x < x by omega] at hc
      simp only [rowFold, nBumps, hb, List.filter_cons, Option.isSome_some] at ih ⊢
      simp only [↓reduceIte, List.length_cons]; omega

theorem nBumps_append (u v : List (Option Nat)) : nBumps (u ++ v) = nBumps u + nBumps v := by
  simp [nBumps]

theorem nBumps_map_some (l : List Nat) : nBumps (l.map some) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [nBumps] at ih ⊢; exact ih

theorem rowFold_append (s : Row) : ∀ (u v : List Nat),
    rowFold s (u ++ v) = ((rowFold (rowFold s u).1 v).1, (rowFold s u).2 ++ (rowFold (rowFold s u).1 v).2)
  | [], v => by simp [rowFold]
  | x :: u, v => by
    simp only [List.cons_append, rowFold, rowFold_append (rowIns x s).1 u v, List.cons_append]

theorem take_succ_getD (l : List Nat) {j : Nat} (h : j < l.length) :
    l.take (j + 1) = l.take j ++ [l.getD j 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; simp [h]

theorem drop_getD (l : List Nat) {j : Nat} (h : j < l.length) :
    l.drop j = l.getD j 0 :: l.drop (j + 1) := by
  rw [List.drop_eq_getElem_cons h]; simp [h]

theorem sorted_take_le {r : Row} (hr : Sorted r) {j : Nat} (hj : j < r.length) :
    ∀ v ∈ r.take j, v ≤ r.getD j 0 := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  simp only [List.length_take] at hi
  have := hr.getD_le (show i ≤ j by omega) hj
  rw [getD_of_lt (by omega)] at this
  simpa using this

/-- While each entry of `r` is smaller than the entry of `s` in the same column, entry `j` of
`r` bumps entry `j` of `s`. -/
theorem rowFold_take {r s : Row} (hr : Sorted r) : ∀ j, j ≤ s.length → j ≤ r.length →
    (∀ i, i < j → r.getD i 0 < s.getD i 0) →
    rowFold s (r.take j) = (r.take j ++ s.drop j, (s.take j).map some)
  | 0, _, _, _ => by simp [rowFold]
  | j + 1, hs, hrl, h => by
    have ih := rowFold_take hr j (by omega) (by omega) (fun i hi => h i (by omega))
    rw [take_succ_getD r (by omega), rowFold_append, ih]
    have e : rowIns (r.getD j 0) (r.take j ++ s.drop j) =
        (r.take j ++ r.getD j 0 :: s.drop (j + 1), some (s.getD j 0)) := by
      rw [Zipper.rowIns_prefix _ _ _ (sorted_take_le hr (by omega)), drop_getD s (by omega)]
      simp only [rowIns, if_pos (h j (by omega))]
    simp only [rowFold, e, take_succ_getD s (show j < s.length by omega)]
    simp

/-- **Fewer bumps.** If entry `j0` of `r` is not smaller than entry `j0` of `s` (and the
earlier ones are), inserting `r` into `s` bumps out fewer than `|s|` entries. -/
theorem rowFold_bumps_lt {r s : Row} (hr : Sorted r) {j0 : Nat} (hj0s : j0 < s.length)
    (hj0r : j0 < r.length) (h : ∀ i, i < j0 → r.getD i 0 < s.getD i 0)
    (hge : s.getD j0 0 ≤ r.getD j0 0) : nBumps (rowFold s r).2 < s.length := by
  have hsplit : r = r.take j0 ++ r.drop j0 := (List.take_append_drop j0 r).symm
  rw [hsplit, rowFold_append, rowFold_take hr j0 (by omega) (by omega) h]
  have hdrop : Sorted (r.drop j0) := hr.sublist (List.drop_sublist _ _)
  have hge' : ∀ x ∈ r.drop j0, r.getD j0 0 ≤ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_drop] at hi
    have := hr.getD_le (show j0 ≤ j0 + i by omega) (by omega)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hj0r,
      show j0 + i < r.length by omega] using this
  have hb := rowFold_bumps_le (r.drop j0) (r.take j0 ++ s.drop j0) (r.getD j0 0) hdrop hge'
  have h1 : ((r.take j0).filter (r.getD j0 0 < ·)).length = 0 := by
    simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro a ha; have := sorted_take_le hr hj0r a ha
    simpa using (show ¬ (r.getD j0 0 < a) by omega)
  have h2 : ((s.drop j0).filter (r.getD j0 0 < ·)).length < (s.drop j0).length := by
    rw [drop_getD s hj0s]
    simp only [List.filter_cons, show ¬ r.getD j0 0 < s.getD j0 0 by omega, decide_false]
    simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
    exact Nat.lt_succ_of_le (List.length_filter_le _ _)
  simp only [List.filter_append, List.length_append] at hb
  simp only [List.length_drop] at h2
  rw [nBumps_append, nBumps_map_some, List.length_take]
  dsimp only
  omega

/-! ### A row on top of a semistandard tableau -/

theorem length_insList (t : Tab) : ∀ xs, (insList t xs).2.length = xs.length
  | [] => rfl
  | x :: xs => by simp [insList, length_insList _ xs]

theorem insList_box (t : Tab) (xs : List Nat) {j : Nat} (hj : j < xs.length) :
    (insList t xs).2.getD j 0 = (ins (xs.getD j 0) (insList t (xs.take j)).1).2 := by
  have e : xs = xs.take j ++ (xs.getD j 0 :: xs.drop (j + 1)) := by
    rw [← drop_getD xs hj, List.take_append_drop]
  conv => lhs; rw [e]
  rw [insList_append]
  simp only [insList]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_insList, List.length_take]; omega)]
  simp [length_insList, Nat.min_eq_left (Nat.le_of_lt hj)]

theorem insList_one_row : ∀ (xs : List Nat) (a : Row), Sorted (a ++ xs) → a ≠ [] →
    insList [a] xs = ([a ++ xs], List.replicate xs.length 0)
  | [], a, _, _ => by simp [insList]
  | x :: xs, a, hs, ha => by
    have hle : ∀ v ∈ a, v ≤ x := fun v hv =>
      (List.pairwise_append.mp hs).2.2 v hv x (by simp)
    have e : ins x [a] = ([a ++ [x]], 0) := by
      rw [ins_cons_none (rowIns_append x a hle)]
    have ih := insList_one_row xs (a ++ [x]) (by simpa using hs) (by simp)
    simp only [insList, e, ih, List.append_assoc, List.singleton_append, List.length_cons,
      List.replicate_succ]

theorem ssyt_length_le : ∀ (s : Row) (rest : Tab), SSYT (s :: rest) →
    ∀ row ∈ rest, row.length ≤ s.length
  | _, [], _ => by simp
  | s, t :: ts, h => by
    intro row hrow
    have h1 : t.length ≤ s.length := h.2.1.1
    rcases List.mem_cons.mp hrow with rfl | hrow
    · exact h1
    · exact Nat.le_trans (ssyt_length_le t ts h.tail row hrow) h1

theorem colH_cons_lt {s : Row} {rest : Tab} {j : Nat} (hj : j < s.length) :
    colH (sh (s :: rest)) j = colH (sh rest) j + 1 := by
  simp [colH, sh, hj]

theorem colH_cons_ge {s : Row} {rest : Tab} (h : SSYT (s :: rest)) {j : Nat}
    (hj : s.length ≤ j) : colH (sh (s :: rest)) j = 0 := by
  simp only [colH, sh, List.map_cons, List.filter_cons, show ¬ j < s.length by omega,
    decide_false, Bool.false_eq_true, ↓reduceIte, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨row, hrow, rfl⟩ := ha
  have := ssyt_length_le s rest h row hrow
  simp; omega

theorem colHeights_drop {sh : List Nat} {L j : Nat} (hj : j < L) :
    (colHeights sh L).drop j = colH sh j :: (colHeights sh L).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simp [colHeights]; omega)]
  simp [colHeights]

/-- **A row on top.** Inserting the entries of `r` into `T`, when `r :: T` is semistandard,
gives `r :: T`; the `j`-th entry creates the box at the bottom of column `j` of `T`. -/
theorem insList_row : ∀ (T : Tab) (r : Row), SSYT (r :: T) →
    insList T r = (r :: T, colHeights (sh T) r.length)
  | [], r, h => by
    have hr := h.good r (by simp)
    obtain ⟨x, xs, rfl⟩ : ∃ x xs, r = x :: xs := by
      cases r with
      | nil => exact absurd rfl hr.2
      | cons x xs => exact ⟨x, xs, rfl⟩
    have e : ins x [] = ([[x]], 0) := rfl
    have := insList_one_row xs [x] hr.1 (by simp)
    simp only [insList, e, this]
    rw [show sh [] = [] from rfl, colHeights, show colH [] = fun _ => 0 from funext fun _ => rfl,
      List.map_const', List.length_range]
    simp [List.replicate_succ]
  | s :: rest, r, h => by
    have hr := (h.good r (by simp)).1
    have hcol : Col2 r s := h.2.1
    have ih := insList_row rest s h.tail
    -- the state after `j` entries of `r`
    have key : ∀ d j, j + d = r.length →
        insList ((r.take j ++ s.drop j) :: (insList rest (s.take j)).1) (r.drop j) =
          (r :: s :: rest, (colHeights (sh (s :: rest)) r.length).drop j) := by
      intro d
      induction d with
      | zero =>
        intro j hj
        have hjr : j = r.length := by omega
        subst hjr
        rw [List.drop_length, List.drop_eq_nil_of_le hcol.1, List.take_of_length_le hcol.1, ih]
        simp [insList, colHeights]
      | succ d ihd =>
        intro j hj
        have hjr : j < r.length := by omega
        rw [drop_getD r hjr]
        simp only [insList]
        by_cases hjs : j < s.length
        · have hlt : r.getD j 0 < s.getD j 0 := by
            have := hcol.2 j hjs
            rwa [getD_of_lt (by omega), getD_of_lt hjs] at this ⊢
          have erow : rowIns (r.getD j 0) (r.take j ++ s.drop j) =
              (r.take (j + 1) ++ s.drop (j + 1), some (s.getD j 0)) := by
            rw [Zipper.rowIns_prefix _ _ _ (sorted_take_le hr hjr), drop_getD s hjs,
              take_succ_getD r hjr]
            simp only [rowIns, if_pos hlt, List.append_assoc, List.singleton_append]
          rw [ins_cons_some erow]
          have estate : (ins (s.getD j 0) (insList rest (s.take j)).1).1 =
              (insList rest (s.take (j + 1))).1 := by
            rw [take_succ_getD s hjs, insList_append]; rfl
          rw [estate, ihd (j + 1) (by omega), colHeights_drop hjr, colH_cons_lt hjs]
          have hbox := insList_box rest s hjs
          rw [ih] at hbox
          simp only [colHeights] at hbox
          rw [← hbox]
          simp [colHeights, hjs]
        · have erow : rowIns (r.getD j 0) (r.take j ++ s.drop j) = (r.take (j + 1), none) := by
            rw [List.drop_eq_nil_of_le (by omega), List.append_nil,
              rowIns_append _ _ (sorted_take_le hr hjr), take_succ_getD r hjr]
          rw [ins_cons_none erow]
          have e1 : s.take (j + 1) = s.take j := by
            rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
          have e2 : s.drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
          have := ihd (j + 1) (by omega)
          rw [e1, e2, List.append_nil] at this
          rw [this, colHeights_drop hjr, colH_cons_ge h.tail (by omega)]
    have := key r.length 0 (by omega)
    simpa [insList] using this

/-! ### Recording tableaux from box rows -/

/-- Add the boxes `bs` to `Q0`, the `i`-th one labelled `ls[i]`. -/
def qFrom (Q0 : Tab) (ls bs : List Nat) : Tab :=
  (ls.zip bs).foldl (fun Q p => tabAdd Q p.2 p.1) Q0

theorem insT_eq (w : List Nat) : ∀ i, i ≤ w.length → insT w i = (insList [] (w.take i)).1
  | 0, _ => rfl
  | i + 1, h => by
    rw [take_succ_getD w (by omega), insList_append, ← insT_eq w i (by omega)]; rfl

theorem qFrom_append (Q0 : Tab) {ls1 bs1 : List Nat} (ls2 bs2 : List Nat)
    (h : ls1.length = bs1.length) :
    qFrom Q0 (ls1 ++ ls2) (bs1 ++ bs2) = qFrom (qFrom Q0 ls1 bs1) ls2 bs2 := by
  simp [qFrom, List.zip_append h, List.foldl_append]

theorem recL_eq (labels w : List Nat) : ∀ i, i ≤ w.length → i ≤ labels.length →
    recL labels w i = qFrom [] (labels.take i) (insList [] (w.take i)).2
  | 0, _, _ => rfl
  | i + 1, h1, h2 => by
    rw [take_succ_getD w (by omega), take_succ_getD labels (by omega), insList_append,
      qFrom_append _ _ _ (by rw [length_insList]; simp; omega), ← recL_eq labels w i (by omega) (by omega),
      ← insT_eq w i (by omega)]
    rfl

theorem sh_qFrom : ∀ (w : List Nat) (T Q0 : Tab) (ls : List Nat), sh Q0 = sh T →
    w.length ≤ ls.length → sh (qFrom Q0 ls (insList T w).2) = sh (insList T w).1
  | [], T, Q0, ls, h, _ => by cases ls <;> simpa [qFrom, insList] using h
  | x :: w, T, Q0, [], _, hl => by simp at hl
  | x :: w, T, Q0, l :: ls, h, hl => by
    have e : qFrom Q0 (l :: ls) (insList T (x :: w)).2 =
        qFrom (tabAdd Q0 (ins x T).2 l) ls (insList (ins x T).1 w).2 := rfl
    rw [e]
    apply sh_qFrom w (ins x T).1 _ ls _ (by simpa using hl)
    rw [sh_tabAdd, h, (sh_ins x T).1]

theorem head_tabAdd_gt {L l : Nat} (hl : L < l) : ∀ (Q : Tab) (b : Nat),
    ((tabAdd Q b l).headD []).filter (· ≤ L) = (Q.headD []).filter (· ≤ L)
  | [], _ => by simp [tabAdd]; omega
  | r :: rs, 0 => by simp [tabAdd]; omega
  | r :: rs, _ + 1 => by simp [tabAdd]

theorem head_qFrom_gt {L : Nat} : ∀ (Q0 : Tab) (ls bs : List Nat), (∀ l ∈ ls, L < l) →
    ((qFrom Q0 ls bs).headD []).filter (· ≤ L) = (Q0.headD []).filter (· ≤ L)
  | Q0, [], bs, _ => by simp [qFrom]
  | Q0, l :: ls, [], _ => by simp [qFrom]
  | Q0, l :: ls, b :: bs, h => by
    have e : qFrom Q0 (l :: ls) (b :: bs) = qFrom (tabAdd Q0 b l) ls bs := rfl
    rw [e, head_qFrom_gt _ ls bs (fun x hx => h x (by simp [hx])),
      head_tabAdd_gt (h l (by simp))]

theorem mem_tabAdd {Q : Tab} {b l x : Nat} (h : x ∈ (tabAdd Q b l).flatten) :
    x ∈ Q.flatten ∨ x = l := by
  induction Q generalizing b with
  | nil => simp [tabAdd] at h; exact Or.inr h
  | cons r rs ih =>
    cases b with
    | zero =>
      simp only [tabAdd, List.flatten_cons, List.mem_append, List.mem_singleton] at h
      rcases h with (h | h) | h
      · exact Or.inl (by simp only [List.flatten_cons]; exact List.mem_append_left _ h)
      · exact Or.inr h
      · exact Or.inl (by simp only [List.flatten_cons]; exact List.mem_append_right _ h)
    | succ b =>
      simp only [tabAdd, List.flatten_cons, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl (by simp [h])
      · rcases ih h with h | h
        · exact Or.inl (by simp only [List.flatten_cons]; exact List.mem_append_right _ h)
        · exact Or.inr h

theorem mem_qFrom : ∀ (Q0 : Tab) (ls bs : List Nat) (x : Nat), x ∈ (qFrom Q0 ls bs).flatten →
    x ∈ Q0.flatten ∨ x ∈ ls
  | Q0, [], bs, x, h => Or.inl (by simpa [qFrom] using h)
  | Q0, l :: ls, [], x, h => Or.inl (by simpa [qFrom] using h)
  | Q0, l :: ls, b :: bs, x, h => by
    have e : qFrom Q0 (l :: ls) (b :: bs) = qFrom (tabAdd Q0 b l) ls bs := rfl
    rw [e] at h
    rcases mem_qFrom _ ls bs x h with h | h
    · rcases mem_tabAdd h with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [h])

theorem headD_sh (t : Tab) : (sh t).headD 0 = (t.headD []).length := by
  cases t <;> rfl

/-- **The first row of `Q` below a label.** If the first `|w1|` labels are `≤ L` and the rest
are `> L`, the entries `≤ L` in the first row of the recording tableau of `w1 ++ w2` are as
many as the boxes of the first row after inserting `w1`. -/
theorem qFrom_head_count (w1 w2 ls1 ls2 : List Nat) (L : Nat) (h1 : ls1.length = w1.length)
    (hle : ∀ l ∈ ls1, l ≤ L) (hgt : ∀ l ∈ ls2, L < l) :
    (((qFrom [] (ls1 ++ ls2) (insList [] (w1 ++ w2)).2).headD []).filter (· ≤ L)).length =
      ((insList [] w1).1.headD []).length := by
  rw [insList_append, qFrom_append _ _ _ (by rw [length_insList]; exact h1),
    head_qFrom_gt _ _ _ hgt]
  have hall : ∀ x ∈ (qFrom [] ls1 (insList [] w1).2).headD [], x ≤ L := by
    intro x hx
    have hx' : x ∈ (qFrom [] ls1 (insList [] w1).2).flatten := by
      cases hq : qFrom [] ls1 (insList [] w1).2 with
      | nil => rw [hq] at hx; simp at hx
      | cons r rs => rw [hq] at hx; simp only [List.flatten_cons]; exact List.mem_append_left _ hx
    rcases mem_qFrom _ _ _ x hx' with h | h
    · simp at h
    · exact hle x h
  rw [List.filter_eq_self.mpr (fun x hx => by simpa using hall x hx), ← headD_sh, ← headD_sh,
    sh_qFrom w1 [] [] ls1 rfl (by omega)]

end RMT.RSK.Fomin
