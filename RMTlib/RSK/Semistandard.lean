import RMTlib.RSK.Nested
import RMTlib.RSK.Zipper

/-!
# Uninsertion preserves semistandardness

The converse theorems `Nested.rsk_unrsk` and `Zipper.rsk_unrsk` assume `Valid`, which asks
for sorted rows and a strictly increasing first column at every stage of uninsertion. This
module removes that assumption: it proves that uninsertion at a corner sends a semistandard
tableau to a semistandard tableau. Then the only condition left on the recording data is the
genuine one, that each index is a corner when it is used (`Peelable`).

The proof is an induction following `Nested.unins`. Besides semistandardness of the result,
it tracks how the top row changed (`Desc`): one entry, at position `k`, was pushed out and
either replaced by a larger value or removed from the end of the row. One row up, that is
exactly what is needed to check the columns, by the classical argument: the value coming up
from position `k` lands at a position `m ≥ k`.

For the zipper version, `Zipper.ins_eq` shows its insertion computes the same function as the
nested one, on all inputs. Uninsertion is then the same on semistandard tableaux too
(`Zipper.unins_eq`), so the result transfers.

## Main results

* `unins_ssyt`: uninsertion at a corner preserves semistandardness.
* `Nested.rsk_unrsk_ssyt`, `Zipper.rsk_unrsk_ssyt`: `rsk (unrsk t is) = (t, is)` for every
  semistandard `t` and every sequence of corners `is`.
* `Zipper.ins_eq`, `Zipper.unins_eq`: the two bumping versions compute the same functions.
-/

namespace RMT.RSK

/-- Row `b` sits correctly under row `a`: it is no longer, and each column strictly
increases. -/
def Col2 (a b : Row) : Prop := b.length ≤ a.length ∧ ∀ k, k < b.length → a.getD k 0 < b.getD k 0

/-- Every column strictly increases and the row lengths weakly decrease. -/
def ColStrictFull : Tab → Prop
  | a :: b :: rest => Col2 a b ∧ ColStrictFull (b :: rest)
  | _ => True

/-- A semistandard Young tableau: rows weakly increase, columns strictly increase, the shape
is a partition, and there are no empty rows. -/
def SSYT (t : Tab) : Prop := Good t ∧ ColStrictFull t

/-- The recording data `is` can be peeled off `t` by `un`, each index a corner when it is
used, down to the empty tableau. -/
def Peelable (un : Nat → Tab → Tab × Nat) : Tab → List Nat → Prop
  | t, [] => t = []
  | t, i :: is => Corner i t ∧ Peelable un (un i t).1 is

/-! ## Sorted rows through `getD` -/

theorem getD_of_lt {r : Row} {i : Nat} (h : i < r.length) : r.getD i 0 = r[i] := by simp [h]

theorem Sorted.getD_le {r : Row} (h : Sorted r) {i j : Nat} (hij : i ≤ j) (hj : j < r.length) :
    r.getD i 0 ≤ r.getD j 0 := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Nat.le_refl _
  · rw [getD_of_lt (by omega), getD_of_lt hj]
    exact List.pairwise_iff_getElem.mp h i j (by omega) hj hlt

theorem sorted_of_getD {r : Row}
    (h : ∀ i j, i < j → j < r.length → r.getD i 0 ≤ r.getD j 0) : Sorted r := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have := h i j hij hj
  rwa [getD_of_lt hi, getD_of_lt hj] at this

/-- A semistandard tableau has a strictly increasing first column. -/
theorem colStrict_of_full : ∀ (t : Tab), Good t → ColStrictFull t → ColStrict t
  | [], _, _ => fun j h => by simp at h
  | [_], _, _ => fun j h => by simp at h
  | a :: b :: rest, hg, hc => by
    intro j hj
    cases j with
    | zero =>
      show Adj a b
      have ha := hg a (by simp)
      have hb := hg b (by simp)
      have hb0 : 0 < b.length := List.length_pos_iff.mpr hb.2
      have ha0 : 0 < a.length := List.length_pos_iff.mpr ha.2
      refine ⟨a[0], List.getElem_mem ha0, fun v hv => ?_⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
      have h1 := hc.1.2 0 hb0
      have h2 := hb.1.getD_le (Nat.zero_le k) hk
      rw [getD_of_lt ha0, getD_of_lt hb0] at h1
      rw [getD_of_lt hb0, getD_of_lt hk] at h2
      omega
    | succ j =>
      have := colStrict_of_full (b :: rest) hg.tail hc.2 j (by simp at hj ⊢; omega)
      simpa using this

theorem SSYT.good {t : Tab} (h : SSYT t) : Good t := h.1

theorem SSYT.colStrict {t : Tab} (h : SSYT t) : ColStrict t := colStrict_of_full t h.1 h.2

theorem SSYT.tail {r : Row} {rs : Tab} (h : SSYT (r :: rs)) : SSYT rs := by
  refine ⟨h.1.tail, ?_⟩
  cases rs with
  | nil => trivial
  | cons s ss => exact h.2.2

/-! ## The value coming up replaces one entry of the row -/

namespace Nested

/-- `rowUnins y r` replaces the entry at some position `m` by `y` and pushes that entry out:
`r[m] < y`, every entry after `m` is `≥ y`, and nothing else changes. -/
theorem rowUnins_spec (y : Nat) : ∀ (r : Row), Sorted r → 0 < r.length → r.getD 0 0 < y →
    ∃ m, m < r.length ∧ r.getD m 0 < y ∧ (∀ j, j < r.length → m < j → y ≤ r.getD j 0) ∧
      (rowUnins y r).2 = r.getD m 0 ∧ (rowUnins y r).1.length = r.length ∧
      ∀ j, (rowUnins y r).1.getD j 0 = if j = m then y else r.getD j 0
  | [], _, h, _ => by simp at h
  | [z], _, _, hz => by
    refine ⟨0, by simp, by simpa using hz, fun j hj h => by simp at hj; omega, by simp [rowUnins],
      by simp [rowUnins], fun j => ?_⟩
    cases j <;> simp [rowUnins]
  | z :: w :: ws, hs, _, hz => by
    have hws : Sorted (w :: ws) := (List.pairwise_cons.mp hs).2
    by_cases hwy : w < y
    · obtain ⟨m, hm, hmy, hafter, h2, hlen, hget⟩ :=
        rowUnins_spec y (w :: ws) hws (by simp) (by simpa using hwy)
      have e : rowUnins y (z :: w :: ws)
          = (z :: (rowUnins y (w :: ws)).1, (rowUnins y (w :: ws)).2) := by
        simp [rowUnins, hwy]
      refine ⟨m + 1, by simp at hm ⊢; omega, by simpa using hmy, fun j hj hmj => ?_,
        by rw [e, h2]; simp, by rw [e]; simp [hlen], fun j => ?_⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simpa using hafter j' (by simp at hj ⊢; omega) (by omega)
      · rw [e]
        cases j with
        | zero => simp
        | succ j => simpa using hget j
    · have hzw : ∀ b ∈ w :: ws, z ≤ b := (List.pairwise_cons.mp hs).1
      have hwws : ∀ b ∈ ws, w ≤ b := (List.pairwise_cons.mp hws).1
      refine ⟨0, by simp, by simpa using hz, fun j hj h0 => ?_, by simp [rowUnins, hwy],
        by simp [rowUnins, hwy], fun j => ?_⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        cases j' with
        | zero => simp; omega
        | succ j'' =>
          have hj'' : j'' < ws.length := by simp at hj; omega
          have := hwws ws[j''] (List.getElem_mem hj'')
          simp only [List.getD_cons_succ, getD_of_lt hj'']; omega
      · cases j <;> simp [rowUnins, hwy]

/-- How the top row changed under uninsertion: the entry at position `k` was pushed out,
and in the new top row `r'` (if the tableau is not empty) either that entry was replaced by a
larger value, no larger than the entries after it, or it was the last entry and was removed. -/
def Desc (r : Row) (t' : Tab) (v : Nat) : Prop :=
  ∃ k, k < r.length ∧ v = r.getD k 0 ∧ ∀ r' rest, t' = r' :: rest →
    (r'.length = r.length ∨ (r'.length + 1 = r.length ∧ k = r'.length)) ∧
    (∀ j, j < r'.length → j ≠ k → r'.getD j 0 = r.getD j 0) ∧
    (k < r'.length → r.getD k 0 < r'.getD k 0 ∧
      ∀ j, j < r.length → k < j → r'.getD k 0 ≤ r.getD j 0)

/-- **Uninsertion at a corner preserves semistandardness**, and changes the top row as
described by `Desc`. Induction following `unins`. -/
theorem unins_ssyt : ∀ (i : Nat) (t : Tab), SSYT t → Corner i t →
    SSYT (unins i t).1 ∧ Desc (t.headD []) (unins i t).1 (unins i t).2
  | _, [], _, ⟨h, _⟩ => by simp at h
  | 0, r :: rs, hss, ⟨_, hcorner⟩ => by
    have hr := hss.1 r (by simp)
    obtain ⟨r0, z, rfl⟩ : ∃ r0 z, r = r0 ++ [z] := by
      rcases List.eq_nil_or_concat r with h | ⟨L, b, h⟩
      · exact absurd h hr.2
      · exact ⟨L, b, by simpa using h⟩
    have hgetD : ∀ j, j < r0.length → (r0 ++ [z]).getD j 0 = r0.getD j 0 := by
      intro j hj
      rw [getD_of_lt (by simp; omega), getD_of_lt hj,
        List.getElem_append_left hj]
    by_cases h0 : r0 = []
    · subst h0
      -- a one-box row at a corner has nothing below it
      have hrs : rs = [] := by
        cases rs with
        | nil => rfl
        | cons s ss =>
          have h1 := hcorner (by simp)
          simp at h1
          exact absurd h1 (hss.1 s (by simp)).2
      subst hrs
      have e : unins 0 [[] ++ [z]] = ([], z) := by simp [unins]
      rw [e]
      exact ⟨⟨fun r h => by simp at h, trivial⟩, 0, by simp, by simp, fun r' rest h => by simp at h⟩
    · have e : unins 0 ((r0 ++ [z]) :: rs) = (r0 :: rs, z) := by simp [unins, h0]
      rw [e]
      refine ⟨⟨fun s hs => ?_, ?_⟩, ⟨r0.length, by simp, by simp, fun r' rest h => ?_⟩⟩
      · simp at hs
        rcases hs with rfl | hs
        · exact ⟨(List.pairwise_append.mp hr.1).1, h0⟩
        · exact hss.1 s (by simp [hs])
      · cases rs with
        | nil => trivial
        | cons s ss =>
          have hc := hss.2
          have h1 := hcorner (by simp)
          simp at h1
          refine ⟨⟨by omega, fun k hk => ?_⟩, hc.2⟩
          rw [← hgetD k (by omega)]
          exact hc.1.2 k hk
      · simp only [List.headD_cons, List.cons.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨Or.inr ⟨by simp, rfl⟩, fun j hj _ => (hgetD j hj).symm, fun h => by omega⟩
  | i + 1, r :: rs, hss, hcorner => by
    have hr := hss.1 r (by simp)
    have hcor := hcorner.tail
    obtain ⟨s, ss, rfl⟩ : ∃ s ss, rs = s :: ss := by
      cases rs with
      | nil => exact absurd hcor.1 (by simp)
      | cons s ss => exact ⟨s, ss, rfl⟩
    have hs := hss.1 s (by simp)
    have hrs : Col2 r s := hss.2.1
    obtain ⟨ihs, k, hk, hy, hdesc⟩ := unins_ssyt i (s :: ss) hss.tail hcor
    -- name the pieces
    generalize hp : unins i (s :: ss) = p at ihs hy hdesc
    obtain ⟨t1, y⟩ := p
    simp only [List.headD] at hk hy hdesc
    have e : unins (i + 1) (r :: s :: ss) = ((rowUnins y r).1 :: t1, (rowUnins y r).2) := by
      simp [unins, hp]
    rw [e]
    show SSYT _ ∧ Desc r _ _
    have hs0 : 0 < s.length := List.length_pos_iff.mpr hs.2
    have hr0 : 0 < r.length := List.length_pos_iff.mpr hr.2
    have hry : r.getD 0 0 < y := by
      have := hrs.2 0 hs0
      have := hs.1.getD_le (Nat.zero_le k) hk
      omega
    obtain ⟨m, hm, hmy, hafter, hv, hlen, hget⟩ := rowUnins_spec y r hr.1 hr0 hry
    have hget' : ∀ j, j ≠ m → (rowUnins y r).1.getD j 0 = r.getD j 0 := fun j hj => by
      simp only [hget j, hj, ↓reduceIte]
    have hgetm : (rowUnins y r).1.getD m 0 = y := by simp only [hget m, ↓reduceIte]
    refine ⟨⟨fun row hrow => ?_, ?_⟩, ⟨m, hm, hv, fun r' rest h => ?_⟩⟩
    · -- every row is sorted and nonempty
      simp at hrow
      rcases hrow with rfl | hrow
      · refine ⟨sorted_of_getD fun a b hab hb => ?_, ?_⟩
        · rw [hlen] at hb
          by_cases ha : a = m
          · subst ha
            rw [hgetm, hget' b (by omega)]; exact hafter b hb hab
          · rw [hget' a ha]
            by_cases hbm : b = m
            · subst hbm; rw [hgetm]
              have := hr.1.getD_le (Nat.le_of_lt hab) hm; omega
            · rw [hget' b hbm]; exact hr.1.getD_le (Nat.le_of_lt hab) hb
        · intro h; have := congrArg List.length h; rw [hlen, List.length_nil] at this; omega
      · exact ihs.1 row hrow
    · -- columns: the new top row over the new second row
      cases t1 with
      | nil => trivial
      | cons s' ss' =>
        refine ⟨?_, ihs.2⟩
        obtain ⟨hl, hsame, hkk⟩ := hdesc s' ss' rfl
        have hs's : s'.length ≤ s.length := by omega
        refine ⟨by rw [hlen]; exact Nat.le_trans hs's hrs.1, fun k' hk' => ?_⟩
        have hk's : k' < s.length := by omega
        by_cases hkm : k' = m
        · subst hkm
          rw [hgetm, hy]
          -- the value from position k of row 1 lands at position m ≥ k of row 0
          have hkm : k ≤ k' := Nat.le_of_not_lt fun h => by
            have h1 := hafter k (by have := hrs.1; omega) h
            have h2 := hrs.2 k hk
            omega
          rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
          · exact (hkk hk').1
          · have h1 := (hkk (by omega)).1
            have h2 := (hkk (by omega)).2 k' hk's hlt
            rw [hsame k' hk' (by omega)]
            omega
        · rw [hget' k' hkm]
          have h1 := hrs.2 k' hk's
          by_cases hkk' : k' = k
          · subst hkk'; have := (hkk hk').1; omega
          · rw [hsame k' hk' hkk']; exact h1
    · -- how row 0 changed
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Or.inl hlen, fun j _ hj => hget' j hj, fun _ => ⟨by omega, fun j hj hmj => by
        rw [hgetm]; exact hafter j hj hmj⟩⟩

/-- A semistandard tableau with peelable recording data satisfies `Valid` at every stage. -/
theorem valid_of_ssyt : ∀ (is : List Nat) (t : Tab), SSYT t → Peelable unins t is →
    Valid unins t is
  | [], _, _, h => h
  | i :: is, t, hss, ⟨hc, hp⟩ =>
    ⟨hss.good, hss.colStrict, hc, valid_of_ssyt is _ (unins_ssyt i t hss hc).1 hp⟩

/-- **Inverse RSK after RSK is the identity** for every semistandard tableau and every
sequence of corners. -/
theorem rsk_unrsk_ssyt (is : List Nat) (t : Tab) (hss : SSYT t) (hp : Peelable unins t is) :
    rsk (unrsk t is) = (t, is) :=
  rsk_unrsk is t (valid_of_ssyt is t hss hp)

end Nested

/-! ## The zipper version computes the same functions -/

namespace Zipper

/-- Row insertion passes over a prefix of entries `≤ x`. -/
theorem rowIns_prefix (x : Nat) (r : Row) : ∀ (l : Row), (∀ p ∈ l, p ≤ x) →
    Nested.rowIns x (l ++ r) = (l ++ (Nested.rowIns x r).1, (Nested.rowIns x r).2)
  | [], _ => rfl
  | p :: l, h => by
    have hp : ¬ x < p := Nat.not_lt.mpr (h p (by simp))
    simp only [List.cons_append, Nested.rowIns, hp, ↓reduceIte]
    rw [rowIns_prefix x r l (fun q hq => h q (by simp [hq]))]

/-- From any state, `go` finishes as nested insertion of `x` into the current row and the
rows below would, with the rows above put back on top. One recursion on `go`'s measure. -/
theorem go_eq (x : Nat) (above : Tab) (pre : Row) : ∀ (row : Row) (below : Tab),
    (∀ p ∈ pre, p ≤ x) →
    go x above pre row below
      = (above.reverse ++ (Nested.ins x ((pre.reverse ++ row) :: below)).1,
         above.length + (Nested.ins x ((pre.reverse ++ row) :: below)).2)
  | [], below, hp => by
    unfold go
    have := Nested.rowIns_append x pre.reverse (by simpa using hp)
    simp [Nested.ins, this]
  | y :: ys, below, hp => by
    unfold go
    split
    · rename_i hxy
      rw [go_eq y _ [] (below.headD []) below.tail (by simp)]
      have hr : Nested.rowIns x (pre.reverse ++ y :: ys) = (pre.reverse ++ x :: ys, some y) := by
        rw [rowIns_prefix x (y :: ys) pre.reverse (by simpa using hp)]
        simp [Nested.rowIns, hxy]
      have hb : Nested.ins y (below.headD [] :: below.tail) = Nested.ins y below := by
        cases below <;> simp [Nested.ins, Nested.rowIns]
      simp only [List.reverse_nil, List.nil_append, hb]
      simp only [Nested.ins, hr, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons]
      congr 1
      omega
    · rename_i hxy
      rw [go_eq x above (y :: pre) ys below (by
        intro p hp'; simp at hp'; rcases hp' with rfl | hp'
        · omega
        · exact hp p hp')]
      simp
termination_by row below => (below.length, row.length)
decreasing_by all_goals (simp_wf; cases below <;> simp [Prod.lex_def] <;> omega)

/-- **The two insertion functions are equal**, on every input. -/
theorem ins_eq (x : Nat) (t : Tab) : ins x t = Nested.ins x t := by
  unfold ins
  rw [go_eq x [] [] (t.headD []) t.tail (by simp)]
  cases t <;> simp [Nested.ins, Nested.rowIns]

/-- On a semistandard tableau, at a corner, the two uninsertion functions agree. -/
theorem unins_eq (i : Nat) (t : Tab) (hss : SSYT t) (hc : Corner i t) :
    unins i t = Nested.unins i t := by
  have hgood : Good (Nested.unins i t).1 := (Nested.unins_ssyt i t hss hc).1.good
  have hins := Nested.ins_unins i t hss.good hss.colStrict hc
  rw [← ins_eq] at hins
  have := unins_ins (Nested.unins i t).2 (Nested.unins i t).1 hgood
  rw [hins] at this
  exact this

/-- A semistandard tableau with peelable recording data satisfies `Valid` at every stage. -/
theorem valid_of_ssyt : ∀ (is : List Nat) (t : Tab), SSYT t → Peelable unins t is →
    Valid unins t is
  | [], _, _, h => h
  | i :: is, t, hss, ⟨hc, hp⟩ => by
    refine ⟨hss.good, hss.colStrict, hc, valid_of_ssyt is _ ?_ hp⟩
    rw [unins_eq i t hss hc]
    exact (Nested.unins_ssyt i t hss hc).1

/-- **Inverse RSK after RSK is the identity** for every semistandard tableau and every
sequence of corners. -/
theorem rsk_unrsk_ssyt (is : List Nat) (t : Tab) (hss : SSYT t) (hp : Peelable unins t is) :
    rsk (unrsk t is) = (t, is) :=
  rsk_unrsk is t (valid_of_ssyt is t hss hp)

end Zipper

end RMT.RSK
