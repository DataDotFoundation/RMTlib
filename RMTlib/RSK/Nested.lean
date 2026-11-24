import RMTlib.RSK.Basic

/-!
# RSK by bumping, as nested structural recursions

The textbook presentation: two structural recursions, one inside the other.

* Level 1, along a row: `rowIns` (bump the first entry `> x`) and `rowUnins` (the value
  coming up replaces the rightmost entry `< y`). Each recurses on the tail of the row.
* Level 2, down the rows: `ins` and `unins` recurse on the list of rows (and, for
  `unins`, on the row index), calling level 1 at each row.
* Level 3, the word: `rsk` and `unrsk`.

Lean accepts every definition as structural recursion, with no termination proof. Every
proof is an ordinary induction with the same shape as the definition it is about, and the
level-2 proofs use the level-1 lemmas at each row.

## Main results

* `rowUnins_rowIns`, `unins_ins`: uninsertion undoes insertion, row by row then whole.
* `rowIns_rowUnins`, `ins_unins`: insertion undoes uninsertion at a corner.
* `unrsk_rsk`, `rsk_unrsk`: both round trips for RSK on words.
-/

namespace RMT.RSK.Nested

open RMT.RSK

/-! ## Level 1: one row -/

/-- Insert `x` into a row: replace the first entry `> x` and return that entry as the bumped one. -/
def rowIns (x : Nat) : Row → Row × Option Nat
  | [] => ([x], none)
  | y :: ys =>
    if x < y then (x :: ys, some y)
    else let p := rowIns x ys; (y :: p.1, p.2)

/-- Reverse bump: `y` comes up from below and replaces the rightmost entry `< y`,
which is pushed out. -/
def rowUnins (y : Nat) : Row → Row × Nat
  | [] => ([], y)                       -- does not occur for valid input
  | [z] => ([y], z)
  | z :: w :: ws =>
    if w < y then let p := rowUnins y (w :: ws); (z :: p.1, p.2)
    else (y :: w :: ws, z)

/-- Level 1 never empties a row. -/
theorem rowIns_ne_nil (x : Nat) : ∀ (r : Row), (rowIns x r).1 ≠ []
  | [] => by simp [rowIns]
  | z :: zs => by unfold rowIns; split <;> simp

/-- The bumped value is always larger than the inserted one. -/
theorem rowIns_bump_gt (x : Nat) : ∀ (r : Row) v, (rowIns x r).2 = some v → x < v
  | [], v, h => by simp [rowIns] at h
  | a :: as, v, h => by
    unfold rowIns at h; split at h
    · simp at h; omega
    · exact rowIns_bump_gt x as v h

/-- After inserting `x`, the row starts with an entry `≤ x`. -/
theorem rowIns_head_le (x : Nat) : ∀ (r : Row) h t, (rowIns x r).1 = h :: t → h ≤ x
  | [], h, t, e => by simp [rowIns] at e; omega
  | a :: as, h, t, e => by
    unfold rowIns at e; split at e
    · simp at e; omega
    · simp at e; omega

/-- Level-1 inverse: undoing a bump gives back the row and the inserted value.
The induction follows `rowIns`. -/
theorem rowUnins_rowIns (x y : Nat) :
    ∀ (r r' : Row), Sorted r → rowIns x r = (r', some y) → rowUnins y r' = (r, x)
  | [], _, _, h => by simp [rowIns] at h
  | z :: zs, r', hs, h => by
    have hz : ∀ b ∈ zs, z ≤ b := (List.pairwise_cons.mp hs).1
    have hzs : Sorted zs := (List.pairwise_cons.mp hs).2
    unfold rowIns at h
    split at h
    · -- x < z: z is bumped, so r' = x :: zs and y = z
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases zs with
      | nil => simp [rowUnins]
      | cons w ws =>
        have : ¬ w < z := Nat.not_lt.mpr (hz w (by simp))
        simp [rowUnins, this]
    · -- z ≤ x: z stays, recurse into zs (this is the induction hypothesis)
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, hb⟩ := h
      have ih := rowUnins_rowIns x y zs _ hzs (Prod.ext rfl hb)
      have hxy : x < y := rowIns_bump_gt x zs y hb
      cases hr : (rowIns x zs).1 with
      | nil => exact absurd hr (rowIns_ne_nil x zs)
      | cons h t =>
        have hh : h < y := Nat.lt_of_le_of_lt (rowIns_head_le x zs h t hr) hxy
        simp only [hr] at ih
        simp [rowUnins, hh, ih]

/-- Level 1 keeps rows sorted. -/
theorem rowIns_sorted (x : Nat) : ∀ (r : Row), Sorted r → Sorted (rowIns x r).1
  | [], _ => by simp [rowIns, Sorted]
  | z :: zs, hs => by
    have hz := (List.pairwise_cons.mp hs).1
    have hzs : Sorted zs := (List.pairwise_cons.mp hs).2
    unfold rowIns; split
    · rename_i hxz
      exact List.pairwise_cons.mpr ⟨fun b hb => Nat.le_trans (Nat.le_of_lt hxz) (hz b hb), hzs⟩
    · rename_i hxz
      refine List.pairwise_cons.mpr ⟨?_, rowIns_sorted x zs hzs⟩
      -- every entry of the new row is an old entry or x, and both are ≥ z
      have mem : ∀ (l : Row) b, b ∈ (rowIns x l).1 → b = x ∨ b ∈ l := by
        intro l; induction l with
        | nil => simp [rowIns]
        | cons a as iha =>
          intro b hb; unfold rowIns at hb; split at hb
          · simp at hb; rcases hb with h | h <;> simp [h]
          · simp at hb; rcases hb with h | h
            · simp [h]
            · rcases iha b h with h' | h' <;> simp [h']
      intro b hb
      rcases mem zs b hb with rfl | h
      · omega
      · exact hz b h

/-- When nothing is bumped, x was appended at the end of the row. -/
theorem rowIns_none (x : Nat) : ∀ (r : Row), (rowIns x r).2 = none → (rowIns x r).1 = r ++ [x]
  | [], _ => by simp [rowIns]
  | z :: zs, h => by
    unfold rowIns at h ⊢; split at h
    · simp at h
    · rename_i hxz; simp [hxz]; exact rowIns_none x zs h

/-! ## Level 2: the tableau -/

/-- Insert `x` into a tableau. Also return the index of the row that gains a box. -/
def ins (x : Nat) : Tab → Tab × Nat
  | [] => ([[x]], 0)
  | r :: rs =>
    match rowIns x r with
    | (r', none) => (r' :: rs, 0)
    | (r', some y) => let p := ins y rs; (r' :: p.1, p.2 + 1)

/-- Remove the last box of row `i` and reverse-bump upward. Returns the ejected value. -/
def unins : Nat → Tab → Tab × Nat
  | _, [] => ([], 0)                                  -- does not occur
  | 0, r :: rs =>
    if r.dropLast = [] then (rs, r.getLast?.getD 0) else (r.dropLast :: rs, r.getLast?.getD 0)
  | i + 1, r :: rs =>
    let p := unins i rs
    let q := rowUnins p.2 r
    (q.1 :: p.1, q.2)

/-- Level-2 inverse. The induction follows `ins` and uses the level-1 lemma at each row. -/
theorem unins_ins (x : Nat) : ∀ (t : Tab), Good t → unins (ins x t).2 (ins x t).1 = (t, x)
  | [], _ => by simp [ins, unins]
  | r :: rs, hg => by
    have hr := hg r (by simp)
    have hrs : Good rs := fun r' h => hg r' (by simp [h])
    unfold ins
    -- case split on the row-level step
    cases hrow : rowIns x r with
    | mk r' b =>
      cases b with
      | none =>
        have happ : r' = r ++ [x] := by
          have := rowIns_none x r (by simp [hrow]); simpa [hrow] using this
        subst happ
        simp [unins, hr.2]
      | some y =>
        simp only [unins]
        rw [unins_ins y rs hrs]
        simp [rowUnins_rowIns x y r r' hr.1 hrow]

/-- Level 2 keeps the tableau valid. -/
theorem ins_good (x : Nat) : ∀ (t : Tab), Good t → Good (ins x t).1
  | [], _ => by
    intro r hr; simp [ins] at hr; subst hr; simp [Sorted]
  | r :: rs, hg => by
    have hr := hg r (by simp)
    have hrs : Good rs := fun r' h => hg r' (by simp [h])
    have hr' : Sorted (rowIns x r).1 ∧ (rowIns x r).1 ≠ [] :=
      ⟨rowIns_sorted x r hr.1, rowIns_ne_nil x r⟩
    unfold ins
    cases hrow : rowIns x r with
    | mk r' b =>
      rw [hrow] at hr'
      cases b with
      | none =>
        intro s hs; simp at hs
        rcases hs with rfl | hs
        · exact hr'
        · exact hrs s hs
      | some y =>
        intro s hs; simp at hs
        rcases hs with rfl | hs
        · exact hr'
        · exact ins_good y rs hrs s hs

/-! ## Level 3: words (RSK proper) -/

/-- RSK on a word, inserting the letters from right to left. Returns the insertion
tableau P and the recording data: the row index of each new box. The recording
tableau Q is determined by these indices. -/
def rsk : List Nat → Tab × List Nat
  | [] => ([], [])
  | x :: w => let p := rsk w; let q := ins x p.1; (q.1, q.2 :: p.2)

/-- Inverse RSK: use the recording data to peel the boxes off again. -/
def unrsk : Tab → List Nat → List Nat
  | _, [] => []
  | t, i :: is => let q := unins i t; q.2 :: unrsk q.1 is

theorem rsk_good : ∀ w, Good (rsk w).1
  | [] => by intro r hr; simp [rsk] at hr
  | x :: w => ins_good x _ (rsk_good w)

/-- RSK is injective: (P, recording data) determines the word. -/
theorem unrsk_rsk : ∀ w, unrsk (rsk w).1 (rsk w).2 = w
  | [] => by simp [rsk, unrsk]
  | x :: w => by
    simp only [rsk, unrsk]
    rw [unins_ins x _ (rsk_good w)]
    simp [unrsk_rsk w]

/-! ## The other direction: insertion undoes uninsertion -/

/-- The value pushed out of a row comes from that row. -/
theorem rowUnins_mem (y : Nat) : ∀ (r : Row), r ≠ [] → (rowUnins y r).2 ∈ r
  | [], h => absurd rfl h
  | [z], _ => by simp [rowUnins]
  | z :: w :: ws, _ => by
    unfold rowUnins
    split
    · exact List.mem_cons_of_mem _ (rowUnins_mem y (w :: ws) (by simp))
    · simp

/-- Level 1: putting the pushed-out value back bumps `y` out again. Induction following
`rowUnins`. -/
theorem rowIns_rowUnins (y : Nat) : ∀ (r : Row), Sorted r → (∃ w ∈ r, w < y) →
    rowIns (rowUnins y r).2 (rowUnins y r).1 = (r, some y)
  | [], _, ⟨_, hw, _⟩ => by simp at hw
  | [z], _, ⟨w, hw, hwy⟩ => by
    simp at hw; subst hw
    simp [rowUnins, rowIns, hwy]
  | z :: w :: ws, hs, ⟨v, hv, hvy⟩ => by
    have hz : ∀ b ∈ w :: ws, z ≤ b := (List.pairwise_cons.mp hs).1
    have hws : Sorted (w :: ws) := (List.pairwise_cons.mp hs).2
    by_cases hwy : w < y
    · have e : rowUnins y (z :: w :: ws)
          = (z :: (rowUnins y (w :: ws)).1, (rowUnins y (w :: ws)).2) := by
        simp [rowUnins, hwy]
      have hle : ¬ (rowUnins y (w :: ws)).2 < z :=
        Nat.not_lt.mpr (hz _ (rowUnins_mem y _ (by simp)))
      rw [e]
      simp only [rowIns, hle, ↓reduceIte]
      rw [rowIns_rowUnins y (w :: ws) hws ⟨w, by simp, hwy⟩]
    · -- the witness must be z: everything after z is ≥ w ≥ y
      have hzy : z < y := by
        simp at hv
        rcases hv with rfl | rfl | hv
        · exact hvy
        · exact absurd hvy hwy
        · have := (List.pairwise_cons.mp hws).1 v hv; omega
      simp [rowUnins, hwy, rowIns, hzy]

/-- Level 1: a value at least every entry of the row is appended at the end. -/
theorem rowIns_append (x : Nat) : ∀ (r : Row), (∀ w ∈ r, w ≤ x) → rowIns x r = (r ++ [x], none)
  | [], _ => rfl
  | z :: zs, h => by
    have hz : ¬ x < z := Nat.not_lt.mpr (h z (by simp))
    simp only [rowIns, hz, ↓reduceIte]
    rw [rowIns_append x zs (fun w hw => h w (by simp [hw]))]
    rfl

/-- The value `unins` pushes out of the tableau comes from its top row. -/
theorem unins_mem : ∀ (i : Nat) (t : Tab), Good t → i < t.length → (unins i t).2 ∈ t.headD []
  | _, [], _, h => by simp at h
  | 0, r :: rs, hg, _ => by
    have hne := (hg r (by simp)).2
    have : r.getLast?.getD 0 ∈ r := by
      rw [List.getLast?_eq_some_getLast hne]; exact List.getLast_mem hne
    unfold unins; split <;> exact this
  | i + 1, r :: rs, hg, _ => rowUnins_mem _ r (hg r (by simp)).2

/-- Level 2: insertion undoes uninsertion at a corner. Induction following `unins`, using the
level-1 lemma at each row. -/
theorem ins_unins : ∀ (i : Nat) (t : Tab), Good t → ColStrict t → Corner i t →
    ins (unins i t).2 (unins i t).1 = (t, i)
  | _, [], _, _, ⟨h, _⟩ => by simp at h
  | 0, r :: rs, hg, _, ⟨_, hcorner⟩ => by
    have hr := hg r (by simp)
    obtain ⟨r0, z, rfl⟩ : ∃ r0 z, r = r0 ++ [z] := by
      rcases List.eq_nil_or_concat r with h | ⟨L, b, h⟩
      · exact absurd h hr.2
      · exact ⟨L, b, by simpa using h⟩
    have hle : ∀ w ∈ r0, w ≤ z := fun w hw =>
      (List.pairwise_append.mp hr.1).2.2 w hw z (by simp)
    by_cases h0 : r0 = []
    · subst h0
      -- a one-box row at a corner has nothing below it
      have hrs : rs = [] := by
        cases rs with
        | nil => rfl
        | cons s ss =>
          have h1 := hcorner (by simp)
          simp at h1
          exact absurd h1 (hg s (by simp)).2
      subst hrs
      simp [unins, ins]
    · have e : unins 0 ((r0 ++ [z]) :: rs) = (r0 :: rs, z) := by simp [unins, h0]
      rw [e]
      simp [ins, rowIns_append z r0 hle]
  | i + 1, r :: rs, hg, hc, hcorner => by
    have hr := hg r (by simp)
    have hcor := hcorner.tail
    have hi : i < rs.length := hcor.1
    -- the value coming up from row 1 is larger than some entry of row 0
    have hmem := unins_mem i rs hg.tail hi
    obtain ⟨w, hw, hwv⟩ : Adj r (rs.headD []) := by
      cases rs with
      | nil => simp at hi
      | cons s ss => exact hc 0 (by simp)
    have hrow := rowIns_rowUnins (unins i rs).2 r hr.1 ⟨w, hw, hwv _ hmem⟩
    simp only [unins, ins, hrow]
    rw [ins_unins i rs hg.tail hc.tail hcor]

/-- **Inverse RSK after RSK is the identity** on recording data that can be peeled off. -/
theorem rsk_unrsk : ∀ (is : List Nat) (t : Tab), Valid unins t is → rsk (unrsk t is) = (t, is)
  | [], t, h => by simp [Valid] at h; subst h; simp [unrsk, rsk]
  | i :: is, t, ⟨hg, hc, hcorner, hv⟩ => by
    simp only [unrsk, rsk]
    rw [rsk_unrsk is _ hv, ins_unins i t hg hc hcorner]

end RMT.RSK.Nested
