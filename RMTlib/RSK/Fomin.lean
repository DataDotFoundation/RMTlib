import RMTlib.RSK.Insert
import RMTlib.Growth.RSK

/-!
# Growth diagrams compute bumping RSK (Fomin)

`RMT.Growth.rsk` builds the growth diagram of a permutation `w` with Fomin's local rule and
reads `P` and `Q` off its top and right edges. This file proves that it computes the bumping
RSK of `RMT.RSK.Nested`, inserting the letters of `w` from left to right (`rsk_eq`).

The proof identifies every shape in the diagram: at row `i` and column `j` it is the shape of
the entries `< j` of the bumping tableau of the first `i` letters (`row_eq`). Two facts make
this work:

* restricting to the entries `< j` commutes with inserting `x < j`, and is unchanged by
  inserting `x ≥ j` (`res_ins_lt`, `res_ins_ge`);
* adding the largest entry `j` back to the restricted tableau changes the insertion of `x` in
  exactly the way the local rule says (`ins_tabAdd`, `localRule_res`).

Mathlib-free.
-/

namespace RMT.RSK.Fomin

open RMT.RSK RMT.RSK.Nested RMT.Growth RMT.Growth.Shape

/-- The entries `< j` of a tableau, down to the first row that has none. -/
def res (j : Nat) : Tab → Tab
  | [] => []
  | r :: rs => if r.filter (· < j) = [] then [] else r.filter (· < j) :: res j rs

/-- The shape of a tableau. -/
def sh (t : Tab) : Shape := t.map List.length

/-! ### Rows -/

theorem rowIns_filter_lt {j x : Nat} (hx : x < j) : ∀ (r : Row), Sorted r →
    (rowIns x r).1.filter (· < j) = (rowIns x (r.filter (· < j))).1 ∧
    (rowIns x (r.filter (· < j))).2 = (rowIns x r).2.filter (· < j)
  | [], _ => by simp [rowIns, hx]
  | z :: zs, hs => by
    have hz := (List.pairwise_cons.mp hs).1
    have hzs : Sorted zs := (List.pairwise_cons.mp hs).2
    by_cases hxz : x < z
    · by_cases hzj : z < j
      · simp [rowIns, hxz, hzj, hx, Option.filter]
      · have hnil : zs.filter (· < j) = [] := by
          rw [List.filter_eq_nil_iff]; intro a ha; have := hz a ha; simp; omega
        simp [rowIns, hxz, hzj, hx, hnil, Option.filter]
    · have hzj : z < j := by omega
      obtain ⟨ih1, ih2⟩ := rowIns_filter_lt hx zs hzs
      simp [rowIns, hxz, hzj, ih1, ih2]

theorem rowIns_filter_ge {j y : Nat} (hy : j ≤ y) : ∀ (r : Row),
    (rowIns y r).1.filter (· < j) = r.filter (· < j) ∧ ∀ z, (rowIns y r).2 = some z → j ≤ z
  | [] => by simp [rowIns, show ¬ y < j by omega]
  | z :: zs => by
    by_cases hyz : y < z
    · simp only [rowIns, hyz, ↓reduceIte]
      refine ⟨?_, fun z' h => ?_⟩
      · simp [show ¬ y < j by omega, show ¬ z < j by omega]
      · cases h; omega
    · obtain ⟨ih1, ih2⟩ := rowIns_filter_ge hy zs
      simp only [rowIns, hyz, ↓reduceIte, List.filter_cons]
      exact ⟨by rw [ih1], ih2⟩

/-! ### Restriction commutes with insertion -/

theorem res_ins_ge {j y : Nat} (hy : j ≤ y) : ∀ (t : Tab), res j (ins y t).1 = res j t
  | [] => by simp [ins, res]; omega
  | r :: rs => by
    obtain ⟨h1, h2⟩ := rowIns_filter_ge hy r
    unfold ins
    cases hrow : rowIns y r with
    | mk r' b =>
      rw [hrow] at h1 h2
      cases b with
      | none => simp only [res, h1]
      | some z =>
        simp only [res, h1]
        rw [res_ins_ge (h2 z rfl) rs]

/-- If no entry of the top row is `< j`, the restriction to entries `< j` is empty. -/
theorem res_eq_nil {j : Nat} {r : Row} {rs : Tab} (h : SSYT (r :: rs))
    (hr : r.filter (· < j) = []) : res j rs = [] := by
  cases rs with
  | nil => rfl
  | cons s ss =>
    obtain ⟨a, ha, hav⟩ : Adj r s := h.colStrict 0 (by simp)
    have hja : j ≤ a := by
      have := List.filter_eq_nil_iff.mp hr a ha; simp at this; exact this
    have : s.filter (· < j) = [] := by
      rw [List.filter_eq_nil_iff]; intro v hv; have := hav v hv; simp; omega
    simp [res, this]

theorem ins_cons_none {x : Nat} {r r' : Row} {rs : Tab} (h : rowIns x r = (r', none)) :
    ins x (r :: rs) = (r' :: rs, 0) := by simp [ins, h]

theorem ins_cons_some {x y : Nat} {r r' : Row} {rs : Tab} (h : rowIns x r = (r', some y)) :
    ins x (r :: rs) = (r' :: (ins y rs).1, (ins y rs).2 + 1) := by simp [ins, h]

theorem res_ins_lt {j x : Nat} (hx : x < j) : ∀ (t : Tab), SSYT t →
    res j (ins x t).1 = (ins x (res j t)).1
  | [], _ => by simp [ins, res, hx]
  | r :: rs, hss => by
    have hr := hss.good r (by simp)
    obtain ⟨h1, h2⟩ := rowIns_filter_lt hx r hr.1
    have hne : (rowIns x (r.filter (· < j))).1 ≠ [] := rowIns_ne_nil _ _
    cases hrow : rowIns x r with
    | mk r' b =>
      rw [hrow] at h1 h2
      simp only at h1 h2
      rw [← h1] at hne
      by_cases hf : r.filter (· < j) = []
      · have hrs := res_eq_nil hss hf
        have hres : res j (r :: rs) = [] := by simp [res, hf]
        rw [hres]
        rw [hf] at h1 h2
        simp only [rowIns] at h1 h2
        cases b with
        | none => rw [ins_cons_none hrow]; simp [res, h1, hrs, ins]
        | some y =>
          have hy : j ≤ y := by
            simp [Option.filter] at h2; exact h2
          rw [ins_cons_some hrow]
          simp only [res, h1]
          rw [res_ins_ge hy, hrs]; simp [ins]
      · have hres : res j (r :: rs) = r.filter (· < j) :: res j rs := by simp [res, hf]
        rw [hres]
        cases b with
        | none =>
          have e : rowIns x (r.filter (· < j)) = (r'.filter (· < j), none) := Prod.ext h1.symm h2
          rw [ins_cons_none hrow, ins_cons_none e]
          simp only [res, hne, ↓reduceIte]
        | some y =>
          by_cases hy : y < j
          · have e : rowIns x (r.filter (· < j)) = (r'.filter (· < j), some y) :=
              Prod.ext h1.symm (by simpa [Option.filter, hy] using h2)
            rw [ins_cons_some hrow, ins_cons_some e]
            simp only [res, hne, ↓reduceIte]
            rw [res_ins_lt hy rs hss.tail]
          · have e : rowIns x (r.filter (· < j)) = (r'.filter (· < j), none) :=
              Prod.ext h1.symm (by simpa [Option.filter, hy] using h2)
            rw [ins_cons_some hrow, ins_cons_none e]
            simp only [res, hne, ↓reduceIte]
            rw [res_ins_ge (by omega)]

/-! ### Shapes -/

theorem sh_tabAdd (v : Nat) : ∀ (u : Tab) (r : Nat), sh (tabAdd u r v) = addRow (sh u) r
  | [], _ => rfl
  | _ :: _, 0 => by simp [tabAdd, sh, addRow]
  | a :: us, r + 1 => by
    have := sh_tabAdd v us r
    simp only [sh] at this ⊢; simp [tabAdd, addRow, this]

theorem sup_self : ∀ l : Shape, sup l l = l
  | [] => rfl
  | a :: xs => by simp [sup, sup_self xs]

theorem sup_addRow_left : ∀ (l : Shape) (r : Nat), sup (addRow l r) l = addRow l r
  | [], _ => rfl
  | a :: xs, 0 => by simp [addRow, sup, sup_self]
  | a :: xs, r + 1 => by simp [addRow, sup, sup_addRow_left xs r]

theorem sup_addRow_right : ∀ (l : Shape) (r : Nat), sup l (addRow l r) = addRow l r
  | [], _ => rfl
  | a :: xs, 0 => by simp [addRow, sup, sup_self]
  | a :: xs, r + 1 => by simp [addRow, sup, sup_addRow_right xs r]

theorem sup_addRow_addRow : ∀ (l : Shape) (r s : Nat), r ≠ s → r ≤ l.length → s ≤ l.length →
    sup (addRow l r) (addRow l s) = addRow (addRow l s) r
  | [], r, s, h, hr, hs => by simp at hr hs; omega
  | a :: xs, 0, 0, h, _, _ => absurd rfl h
  | a :: xs, 0, s + 1, _, _, _ => by
    simp [addRow, sup, sup_addRow_right]
  | a :: xs, r + 1, 0, _, _, _ => by
    simp [addRow, sup, sup_addRow_left]
  | a :: xs, r + 1, s + 1, h, hr, hs => by
    simp [addRow, sup]
    exact sup_addRow_addRow xs r s (by omega) (by simpa using hr) (by simpa using hs)

theorem addRow_ne : ∀ (l : Shape) (r : Nat), addRow l r ≠ l
  | [], _ => by simp [addRow]
  | a :: xs, 0 => by simp [addRow]
  | a :: xs, r + 1 => by simp [addRow]; exact addRow_ne xs r

theorem addRow_inj : ∀ (l : Shape) (r s : Nat), r ≤ l.length → s ≤ l.length →
    addRow l r = addRow l s → r = s
  | [], r, s, hr, hs, _ => by simp at hr hs; omega
  | a :: xs, 0, 0, _, _, _ => rfl
  | a :: xs, 0, s + 1, _, _, h => by simp [addRow] at h
  | a :: xs, r + 1, 0, _, _, h => by simp [addRow] at h
  | a :: xs, r + 1, s + 1, hr, hs, h => by
    simp [addRow] at h
    rw [addRow_inj xs r s (by simpa using hr) (by simpa using hs) h]

theorem diffRow_addRow : ∀ (l : Shape) (r : Nat), r ≤ l.length → diffRow (addRow l r) l = r
  | [], r, hr => by simp at hr; subst hr; rfl
  | a :: xs, 0, _ => by simp [addRow, diffRow]
  | a :: xs, r + 1, hr => by
    simp [addRow, diffRow, diffRow_addRow xs r (by simpa using hr)]

/-! ### Insertion adds one box -/

theorem rowIns_length_some (x : Nat) : ∀ (r : Row) y, (rowIns x r).2 = some y →
    (rowIns x r).1.length = r.length
  | [], y, h => by simp [rowIns] at h
  | z :: zs, y, h => by
    unfold rowIns at h ⊢; split
    · simp
    · rename_i hxz; simp only [hxz, ↓reduceIte] at h
      simp [rowIns_length_some x zs y h]

theorem rowIns_mem_bump (x : Nat) : ∀ (r : Row) y, (rowIns x r).2 = some y → y ∈ r
  | [], y, h => by simp [rowIns] at h
  | z :: zs, y, h => by
    unfold rowIns at h; split at h
    · simp at h; simp [h]
    · exact List.mem_cons_of_mem _ (rowIns_mem_bump x zs y h)

theorem sh_ins (x : Nat) : ∀ (t : Tab),
    sh (ins x t).1 = addRow (sh t) (ins x t).2 ∧ (ins x t).2 ≤ t.length
  | [] => by simp [ins, sh, addRow]
  | r :: rs => by
    cases hrow : rowIns x r with
    | mk r' b =>
      cases b with
      | none =>
        rw [ins_cons_none hrow]
        have : r' = r ++ [x] := by simpa [hrow] using rowIns_none x r (by simp [hrow])
        subst this; simp [sh, addRow]
      | some y =>
        rw [ins_cons_some hrow]
        have hl : r'.length = r.length := by
          simpa [hrow] using rowIns_length_some x r y (by simp [hrow])
        obtain ⟨ih1, ih2⟩ := sh_ins y rs
        simp only [sh] at ih1 ⊢
        simp [addRow, hl, ih1]; omega

/-- Inserting a value at least every entry of the top row appends it there. -/
theorem ins_max {x : Nat} : ∀ (u : Tab), (∀ v ∈ u.headD [], v ≤ x) → ins x u = (tabAdd u 0 x, 0)
  | [], _ => rfl
  | r :: rs, h => by
    rw [ins_cons_none (rowIns_append x r h)]; rfl

/-! ### Insertion below a new largest entry -/

theorem rowIns_append_max {v j : Nat} (hv : v < j) : ∀ (row : Row),
    rowIns v (row ++ [j]) = match rowIns v row with
      | (row', some y) => (row' ++ [j], some y)
      | (row', none) => (row', some j)
  | [] => by simp [rowIns, hv]
  | z :: zs => by
    by_cases hvz : v < z
    · simp [rowIns, hvz]
    · have ih := rowIns_append_max hv zs
      simp only [List.cons_append, rowIns, hvz, ↓reduceIte, ih]
      cases rowIns v zs with
      | mk a b => cases b <;> rfl

/-- All entries of a tableau are `< j`. -/
def AllLt (j : Nat) (u : Tab) : Prop := ∀ row ∈ u, ∀ v ∈ row, v < j

theorem ins_tabAdd {j : Nat} : ∀ (u : Tab) (r x : Nat), x < j → AllLt j u → r ≤ u.length →
    ins x (tabAdd u r j) = if (ins x u).2 = r then (tabAdd (ins x u).1 (r + 1) j, r + 1)
      else (tabAdd (ins x u).1 r j, (ins x u).2)
  | [], r, x, hx, _, hr => by
    simp at hr; subst hr
    simp [tabAdd, ins, rowIns, hx]
  | row :: us, 0, x, hx, hu, _ => by
    have hrow' := rowIns_append_max hx row
    cases hrow : rowIns x row with
    | mk row' b =>
      rw [hrow] at hrow'
      cases b with
      | none =>
        simp only at hrow'
        have e : tabAdd (row :: us) 0 j = (row ++ [j]) :: us := rfl
        rw [e, ins_cons_some hrow', ins_cons_none hrow]
        have hmax : ∀ v ∈ us.headD [], v ≤ j := by
          cases us with
          | nil => simp
          | cons s ss => intro v hv; exact Nat.le_of_lt (hu s (by simp) v hv)
        rw [ins_max us hmax]; rfl
      | some y =>
        simp only at hrow'
        have e : tabAdd (row :: us) 0 j = (row ++ [j]) :: us := rfl
        rw [e, ins_cons_some hrow', ins_cons_some hrow]
        simp [tabAdd]
  | row :: us, r + 1, x, hx, hu, hr => by
    have e : tabAdd (row :: us) (r + 1) j = row :: tabAdd us r j := rfl
    rw [e]
    cases hrow : rowIns x row with
    | mk row' b =>
      cases b with
      | none =>
        rw [ins_cons_none hrow, ins_cons_none hrow]; simp [tabAdd]
      | some y =>
        rw [ins_cons_some hrow, ins_cons_some hrow]
        have hy : y < j := hu row (by simp) y (rowIns_mem_bump x row y (by simp [hrow]))
        rw [ins_tabAdd us r y hy (fun s hs => hu s (by simp [hs])) (by simpa using hr)]
        by_cases hs : (ins y us).2 = r
        · simp [hs, tabAdd]
        · simp [hs, tabAdd]

/-! ### Restricting to `< j + 1` adds the box of `j` -/

theorem res_succ_of_not_mem {j : Nat} : ∀ (t : Tab), j ∉ t.flatten → res (j + 1) t = res j t
  | [], _ => rfl
  | r :: rs, h => by
    have hr : r.filter (· < j + 1) = r.filter (· < j) := by
      apply List.filter_congr; intro v hv
      have : v ≠ j := fun e => h (by rw [List.flatten_cons]; exact List.mem_append_left _ (e ▸ hv))
      simp; omega
    have ih := res_succ_of_not_mem rs
      (fun e => h (by rw [List.flatten_cons]; exact List.mem_append_right _ e))
    simp only [res, hr, ih]

theorem allLt_res (j : Nat) : ∀ (t : Tab), AllLt j (res j t)
  | [] => by intro row h; simp [res] at h
  | r :: rs => by
    intro row h v hv
    simp only [res] at h; split at h
    · simp at h
    · simp at h; rcases h with rfl | h
      · simp at hv; exact hv.2
      · exact allLt_res j rs row h v hv

theorem length_res_le (j : Nat) : ∀ (t : Tab), (res j t).length ≤ t.length
  | [] => by simp [res]
  | r :: rs => by
    simp only [res]; split
    · simp
    · simp [length_res_le j rs]

/-- Every entry below a row whose entries are all `≥ j` is `> j`. -/
theorem gt_below {j : Nat} : ∀ (r : Row) (rs : Tab), SSYT (r :: rs) → (∀ a ∈ r, j ≤ a) →
    ∀ v ∈ rs.flatten, j < v
  | _, [], _, _ => by simp
  | r, s :: ss, h, hr => by
    obtain ⟨a, ha, hav⟩ : Adj r s := h.colStrict 0 (by simp)
    have hs : ∀ v ∈ s, j < v := fun v hv => Nat.lt_of_le_of_lt (hr a ha) (hav v hv)
    have := gt_below s ss h.tail (fun v hv => Nat.le_of_lt (hs v hv))
    intro v hv; simp at hv
    rcases hv with hv | ⟨l, hl, hvl⟩
    · exact hs v hv
    · have := gt_below s ss h.tail (fun v hv => Nat.le_of_lt (hs v hv)) v
        (by simp; exact ⟨l, hl, hvl⟩)
      exact this

theorem filter_succ_of_mem {j : Nat} : ∀ (r : Row), Sorted r → r.Nodup → j ∈ r →
    r.filter (· < j + 1) = r.filter (· < j) ++ [j]
  | [], _, _, h => by simp at h
  | z :: zs, hs, hnd, h => by
    have hz := (List.pairwise_cons.mp hs).1
    have hzs : Sorted zs := (List.pairwise_cons.mp hs).2
    have hzn := (List.nodup_cons.mp hnd)
    by_cases hzj : z = j
    · subst hzj
      have hgt : ∀ a ∈ zs, z < a := fun a ha => by
        have := hz a ha; have : a ≠ z := fun e => hzn.1 (e ▸ ha); omega
      have h1 : zs.filter (· < z + 1) = [] := by
        rw [List.filter_eq_nil_iff]; intro a ha; have := hgt a ha; simp; omega
      have h2 : zs.filter (· < z) = [] := by
        rw [List.filter_eq_nil_iff]; intro a ha; have := hgt a ha; simp; omega
      simp [h1, h2]
    · have hj : j ∈ zs := (List.mem_cons.mp h).resolve_left (fun e => hzj e.symm)
      have hzlt : z < j := by have := hz j hj; omega
      simp [hzlt, show z < j + 1 by omega,
        filter_succ_of_mem zs hzs hzn.2 hj]

/-- **The box of `j`.** In a semistandard tableau with distinct entries containing `j`, the
entries `< j + 1` are those `< j` with `j` added at the end of some row. -/
theorem res_succ_of_mem {j : Nat} : ∀ (t : Tab), SSYT t → t.flatten.Nodup → j ∈ t.flatten →
    ∃ r, r ≤ (res j t).length ∧ res (j + 1) t = tabAdd (res j t) r j
  | [], _, _, h => by simp at h
  | row :: rs, hss, hnd, h => by
    have hrow := hss.good row (by simp)
    have hnd' : row.Nodup ∧ rs.flatten.Nodup ∧ ∀ a ∈ row, a ∉ rs.flatten := by
      simp only [List.flatten_cons, List.nodup_append] at hnd
      exact ⟨hnd.1, hnd.2.1, fun a ha hb => hnd.2.2 a ha a hb rfl⟩
    by_cases hj : j ∈ row
    · have hf := filter_succ_of_mem row hrow.1 hnd'.1 hj
      have hrs : res (j + 1) rs = res j rs := res_succ_of_not_mem rs (hnd'.2.2 j hj)
      by_cases hn : row.filter (· < j) = []
      · refine ⟨0, Nat.zero_le _, ?_⟩
        have hall : ∀ a ∈ row, j ≤ a := fun a ha => by
          have := List.filter_eq_nil_iff.mp hn a ha; simp at this; exact this
        have hres : res j rs = [] := res_eq_nil hss hn
        simp [res, hf, hn, hrs, hres, tabAdd]
      · refine ⟨0, Nat.zero_le _, ?_⟩
        simp [res, hf, hn, hrs, tabAdd]
    · have hf : row.filter (· < j + 1) = row.filter (· < j) := by
        apply List.filter_congr; intro v hv
        have : v ≠ j := fun e => hj (e ▸ hv)
        simp; omega
      have hj' : j ∈ rs.flatten := by simp at h ⊢; rcases h with h | h; exact absurd h hj; exact h
      by_cases hn : row.filter (· < j) = []
      · exfalso
        have hall : ∀ a ∈ row, j ≤ a := fun a ha => by
          have := List.filter_eq_nil_iff.mp hn a ha; simp at this; exact this
        have := gt_below row rs hss hall j hj'
        omega
      · obtain ⟨r, hr, e⟩ := res_succ_of_mem rs hss.tail hnd'.2.1 hj'
        refine ⟨r + 1, by simp [res, hn]; exact hr, ?_⟩
        simp [res, hf, hn, e, tabAdd]

/-! ### The local rule -/

/-- **Fomin's local rule holds for bumping.** Around the square of the growth diagram at
value `j` and the insertion of `x`, the four shapes are those of the restrictions of `P` and
of `ins x P` to the entries `< j` and `< j + 1`. -/
theorem localRule_res (P : Tab) (hP : SSYT P) (hnd : P.flatten.Nodup) (x : Nat)
    (hx : x ∉ P.flatten) (j : Nat) :
    sh (res (j + 1) (ins x P).1) =
      localRule (sh (res j P)) (sh (res (j + 1) P)) (sh (res j (ins x P).1)) (x == j) := by
  -- `μ` is `ρ`, or `ρ` plus the box of `j`
  have hμ : res (j + 1) P = res j P ∨
      ∃ r, r ≤ (res j P).length ∧ res (j + 1) P = tabAdd (res j P) r j := by
    by_cases hj : j ∈ P.flatten
    · exact Or.inr (res_succ_of_mem P hP hnd hj)
    · exact Or.inl (res_succ_of_not_mem P hj)
  rcases Nat.lt_trichotomy j x with hjx | rfl | hxj
  · -- `x > j`: nothing changes below `j + 1`
    rw [res_ins_ge (Nat.le_of_lt hjx), res_ins_ge hjx]
    have hb : (x == j) = false := by simp; omega
    rw [hb]
    rcases hμ with e | ⟨r, _, e⟩
    · rw [e]; simp [localRule]
    · rw [e, sh_tabAdd]
      simp [localRule, addRow_ne, sup_addRow_left]
  · -- `x = j`: a box in the first row
    have hj : res (j + 1) P = res j P := res_succ_of_not_mem P hx
    rw [res_ins_ge (Nat.le_refl j), res_ins_lt (Nat.lt_succ_self j) P hP, hj]
    have hmax : ∀ v ∈ (res j P).headD [], v ≤ j := by
      intro v hv
      cases h : res j P with
      | nil => rw [h] at hv; simp at hv
      | cons row rows =>
        rw [h] at hv
        exact Nat.le_of_lt (allLt_res j P row (by rw [h]; simp) v hv)
    rw [ins_max _ hmax, sh_tabAdd]
    simp [localRule]
  · -- `x < j`
    rw [res_ins_lt hxj P hP, res_ins_lt (Nat.lt_succ_of_lt hxj) P hP]
    have hb : (x == j) = false := by simp; omega
    rw [hb]
    obtain ⟨hsh, hs⟩ := sh_ins x (res j P)
    rcases hμ with e | ⟨r, hr, e⟩
    · rw [e, hsh]
      simp [localRule, Ne.symm (addRow_ne _ _), sup_addRow_right]
    · rw [e, ins_tabAdd (res j P) r x hxj (allLt_res j P) hr, sh_tabAdd, hsh]
      have hsl : (ins x (res j P)).2 ≤ (sh (res j P)).length := by simpa [sh] using hs
      have hrl : r ≤ (sh (res j P)).length := by simpa [sh] using hr
      by_cases hsr : (ins x (res j P)).2 = r
      · rw [if_pos hsr]
        simp only [sh_tabAdd, hsh, hsr]
        simp [localRule, addRow_ne, diffRow_addRow _ _ hrl]
      · rw [if_neg hsr]
        simp only [sh_tabAdd, hsh]
        have hne : addRow (sh (res j P)) r ≠ addRow (sh (res j P)) (ins x (res j P)).2 :=
          fun h => hsr (addRow_inj _ _ _ hsl hrl h.symm)
        simp [localRule, hne, sup_addRow_addRow _ _ _ (Ne.symm hsr) hrl hsl]

/-! ### Entries -/

theorem rowIns_perm (x : Nat) : ∀ (r : Row), ((rowIns x r).1 ++ (rowIns x r).2.toList).Perm (x :: r)
  | [] => by simp [rowIns]
  | z :: zs => by
    by_cases hxz : x < z
    · simp only [rowIns, hxz, ↓reduceIte, Option.toList_some]
      exact List.Perm.cons x (List.perm_append_comm (l₁ := zs) (l₂ := [z]))
    · simp only [rowIns, hxz, ↓reduceIte, List.cons_append]
      exact ((rowIns_perm x zs).cons z).trans (List.Perm.swap x z zs)

theorem ins_perm (x : Nat) : ∀ (t : Tab), (ins x t).1.flatten.Perm (x :: t.flatten)
  | [] => by simp [ins]
  | r :: rs => by
    have hp := rowIns_perm x r
    cases hrow : rowIns x r with
    | mk r' b =>
      rw [hrow] at hp
      cases b with
      | none =>
        rw [ins_cons_none hrow]; simp only [Option.toList_none, List.append_nil] at hp
        simp only [List.flatten_cons]
        exact hp.append_right _
      | some y =>
        rw [ins_cons_some hrow]; simp only [Option.toList_some] at hp
        simp only [List.flatten_cons]
        refine ((ins_perm y rs).append_left r').trans ?_
        rw [show r' ++ y :: rs.flatten = (r' ++ [y]) ++ rs.flatten by simp]
        exact hp.append_right _

theorem res_of_allLt {j : Nat} : ∀ (t : Tab), Good t → AllLt j t → res j t = t
  | [], _, _ => rfl
  | r :: rs, hg, h => by
    have hr : r.filter (· < j) = r := by
      rw [List.filter_eq_self]; intro a ha; simpa using h r (by simp) a ha
    simp [res, hr, (hg r (by simp)).2, res_of_allLt rs hg.tail (fun s hs => h s (by simp [hs]))]

theorem res_zero : ∀ (t : Tab), res 0 t = []
  | [] => rfl
  | r :: rs => by simp [res]

/-! ### The growth diagram, row by row -/

/-- The bumping tableau of the first `i` letters of `w`, inserted left to right. -/
def insT (w : List Nat) : Nat → Tab
  | 0 => []
  | i + 1 => (ins (w.getD i 0) (insT w i)).1

/-- The recording tableau of the first `i` letters: letter `i + 1` labels the new box. -/
def recT (w : List Nat) : Nat → Tab
  | 0 => []
  | i + 1 => tabAdd (recT w i) (ins (w.getD i 0) (insT w i)).2 (i + 1)

theorem insT_ssyt (w : List Nat) : ∀ i, SSYT (insT w i)
  | 0 => ⟨fun r hr => by simp [insT] at hr, trivial⟩
  | i + 1 => (ins_ssyt _ _ (insT_ssyt w i)).1

theorem insT_perm (w : List Nat) : ∀ i, i ≤ w.length → (insT w i).flatten.Perm (w.take i)
  | 0, _ => by simp [insT]
  | i + 1, h => by
    have ih := insT_perm w i (by omega)
    simp only [insT, List.take_add_one]
    have hi : w[i]? = some (w.getD i 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [hi]
    exact (ins_perm _ _).trans ((ih.cons _).trans
      (by simpa using List.perm_append_comm (l₁ := [w.getD i 0]) (l₂ := w.take i)))

/-- The inner recursion of the growth diagram, for rows given by functions of the column. -/
theorem nextRow_eq (x : Nat) (L L' : Nat → Shape)
    (hloc : ∀ j, localRule (L j) (L (j + 1)) (L' j) (x == j) = L' (j + 1)) :
    ∀ m j, nextRow x ((List.range' j (m + 1)).map L) (L' j) j = (List.range' (j + 1) m).map L'
  | 0, j => by simp [nextRow]
  | m + 1, j => by
    have ih := nextRow_eq x L L' hloc m (j + 1)
    rw [List.range'_succ, List.map_cons] at ih
    simp only [List.range'_succ, List.map_cons, nextRow, hloc, ih]

/-- **The growth diagram, row by row**: the shape at row `i`, column `j` is the shape of the
entries `< j` of the bumping tableau of the first `i` letters. -/
theorem row_eq (w : List Nat) (hw : w.Perm (List.range w.length)) :
    ∀ i, i ≤ w.length → row w i = (List.range (w.length + 1)).map fun j => sh (res j (insT w i))
  | 0, _ => by
    simp only [row, insT]
    apply List.ext_getElem <;> simp [res, sh]
  | i + 1, h => by
    have hnd : w.Nodup := hw.nodup_iff.mpr List.nodup_range
    have ih := row_eq w hw i (by omega)
    have hP := insT_perm w i (by omega)
    have hndP : (insT w i).flatten.Nodup := hP.nodup_iff.mpr ((List.take_sublist _ _).nodup hnd)
    have hx : w.getD i 0 ∉ (insT w i).flatten := by
      intro hm
      have hm' := hP.mem_iff.mp hm
      have hi : i < w.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hm'
      obtain ⟨k, hk, e⟩ := List.getElem_of_mem hm'
      rw [List.getElem_take] at e
      have := (List.getElem_inj hnd).mp e
      simp at hk; omega
    simp only [row]
    rw [ih]; simp only [List.range_eq_range']
    have := nextRow_eq (w.getD i 0) (fun j => sh (res j (insT w i)))
      (fun j => sh (res j (insT w (i + 1))))
      (fun j => (localRule_res _ (insT_ssyt w i) hndP _ hx j).symm) w.length 0
    rw [res_zero, show sh [] = [] from rfl] at this
    rw [this, List.range'_succ]
    simp [res_zero, sh]

/-! ### Reading off the tableaux -/

/-- `chainToTableau` along a chain given as a function, when each step adds the next box. -/
theorem chain_eq (S : Nat → Shape) (T : Nat → Tab) (N : Nat)
    (hstep : ∀ k, k < N → tabAdd (T k) (diffRow (S (k + 1)) (S k)) (k + 1) = T (k + 1)) :
    ∀ m k, k + m ≤ N → chainToTableau ((List.range' k (m + 1)).map S) k (T k) = T (k + m)
  | 0, k, _ => by simp [chainToTableau]
  | m + 1, k, h => by
    have ih := chain_eq S T N hstep m (k + 1) (by omega)
    rw [List.range'_succ, List.map_cons] at ih ⊢
    rw [List.range'_succ, List.map_cons]
    simp only [chainToTableau]
    rw [hstep k (by omega), ih]; congr 1; omega

theorem map_tabAdd (f : Nat → Nat) (v : Nat) : ∀ (u : Tab) (r : Nat),
    (tabAdd u r v).map (·.map f) = tabAdd (u.map (·.map f)) r (f v)
  | [], _ => rfl
  | _ :: _, 0 => by simp [tabAdd]
  | a :: us, r + 1 => by simp [tabAdd, map_tabAdd f v us r]

theorem allLt_insT (w : List Nat) (hw : w.Perm (List.range w.length)) (i : Nat)
    (hi : i ≤ w.length) : AllLt w.length (insT w i) := by
  intro row hrow v hv
  have hm : v ∈ (insT w i).flatten := List.mem_flatten.mpr ⟨row, hrow, hv⟩
  have := (hw.mem_iff.mp (List.mem_of_mem_take ((insT_perm w i hi).mem_iff.mp hm)))
  simpa using this

/-- **Fomin's theorem.** For a permutation `w` of `0, …, n-1`, the growth-diagram RSK
(`RMT.Growth.rsk`) returns the bumping insertion tableau of `w` (entries shifted to
`1, …, n`) and its recording tableau. -/
theorem rsk_eq (w : List Nat) (hw : w.Perm (List.range w.length)) :
    RMT.Growth.rsk w = ((insT w w.length).map (·.map (· + 1)), recT w w.length) := by
  have hrow := row_eq w hw
  simp only [RMT.Growth.rsk]
  have htop : ((List.range (w.length + 1)).map (row w)).getLastD [] = row w w.length := by
    simp [List.getLastD_eq_getLast?, List.getLast?_map, List.getLast?_range]
  have hright : ((List.range (w.length + 1)).map (row w)).map (·.getLastD []) =
      (List.range' 0 (w.length + 1)).map fun i => sh (insT w i) := by
    rw [List.map_map, List.range_eq_range']
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range'_1] at hi
    simp only [Function.comp, hrow i (by omega)]
    rw [List.getLastD_eq_getLast?, List.getLast?_map, List.getLast?_range]
    simp [res_of_allLt _ (insT_ssyt w i).good (allLt_insT w hw i (by omega))]
  rw [htop, hright, hrow w.length (Nat.le_refl _), List.range_eq_range']
  have hP := insT_perm w w.length (Nat.le_refl _)
  rw [List.take_length] at hP
  have hnd : (insT w w.length).flatten.Nodup := hP.nodup_iff.mpr (hw.nodup_iff.mpr List.nodup_range)
  have hstepP : ∀ k, k < w.length →
      tabAdd ((res k (insT w w.length)).map (·.map (· + 1))) (diffRow (sh (res (k + 1) (insT w w.length))) (sh (res k (insT w w.length)))) (k + 1)
        = (res (k + 1) (insT w w.length)).map (·.map (· + 1)) := by
    intro k hk
    have hkm : k ∈ (insT w w.length).flatten := hP.mem_iff.mpr (hw.mem_iff.mpr (List.mem_range.mpr hk))
    obtain ⟨r, hr, e⟩ := res_succ_of_mem (insT w w.length) (insT_ssyt w _) hnd hkm
    rw [e, sh_tabAdd, diffRow_addRow _ _ (by simpa [sh] using hr), map_tabAdd]
  have hP' := chain_eq (fun j => sh (res j (insT w w.length))) (fun j => (res j (insT w w.length)).map (·.map (· + 1)))
    w.length hstepP w.length 0 (by omega)
  simp only [res_zero, List.map_nil, Nat.zero_add] at hP'
  have hstepQ : ∀ k, k < w.length + 1 →
      tabAdd (recT w k) (diffRow (sh (insT w (k + 1))) (sh (insT w k))) (k + 1) = recT w (k + 1) := by
    intro k _
    obtain ⟨h1, h2⟩ := sh_ins (w.getD k 0) (insT w k)
    simp only [insT, recT]
    rw [h1, diffRow_addRow _ _ (by simpa [sh] using h2)]
  have hQ' := chain_eq (fun i => sh (insT w i)) (recT w) (w.length + 1) hstepQ w.length 0 (by omega)
  simp only [Nat.zero_add, show recT w 0 = [] from rfl] at hQ'
  rw [hP', hQ', res_of_allLt _ (insT_ssyt w _).good (allLt_insT w hw _ (Nat.le_refl _))]

end RMT.RSK.Fomin
