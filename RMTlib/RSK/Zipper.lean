import RMTlib.RSK.Basic

/-!
# RSK by bumping, as tail recursions over a zipper

Insertion `go` and uninsertion `up` are each ONE tail-recursive function over a cursor
into the tableau: the rows above (nearest first), the current row split at the cursor, and
the rows below. Neither of the two arguments that shrink decreases on every call, so both
functions are well-founded recursions on a lexicographic measure:

* `go` (going down): `(below.length, row.length)`. Moving right shortens the row; a bump
  shortens `below`.
* `up` (going up): `(above.length, rev.length)`. Moving left shortens the row; passing a
  value up shortens `above`.

Each step of `go` is undone by a step of `up`. Each main proof is again one recursion on
the same measure, stated for every intermediate state of the loop (generalising the
accumulators `pre` and `above`) and relating it to the final answer of the other loop.

## Main results

* `unins_go` / `unins_ins`: uninsertion undoes insertion (recursion on `go`'s measure).
* `ins_up` / `ins_unins`: insertion undoes uninsertion at a corner (recursion on `up`'s).
* `unrsk_rsk`, `rsk_unrsk`: both round trips for RSK on words.
-/

namespace RMT.RSK.Zipper

open RMT.RSK

/-- Put a row on top, leaving out an empty row. -/
def mk (r : Row) (b : Tab) : Tab := if r = [] then b else r :: b

/-! ## Forward: one recursion, going down -/

/-- Insert `x`. State: `above` (rows above, nearest first), the current row
`pre.reverse ++ row` with the cursor between `pre` and `row`, and `below`. Returns the new
tableau and the index of the row that gained a box. Measure `(below.length, row.length)`. -/
def go (x : Nat) (above : Tab) (pre : Row) : Row → Tab → Tab × Nat
  | [], below => (above.reverse ++ (pre.reverse ++ [x]) :: below, above.length)
  | y :: ys, below =>
    if x < y then go y ((pre.reverse ++ x :: ys) :: above) [] (below.headD []) below.tail
    else go x above (y :: pre) ys below
termination_by row below => (below.length, row.length)
decreasing_by all_goals (simp_wf; cases below <;> simp [Prod.lex_def] <;> omega)

/-- Insert `x` into a tableau, returning the row index of the new box. -/
def ins (x : Nat) (t : Tab) : Tab × Nat := go x [] [] (t.headD []) t.tail

/-! ## Inverse: one recursion, going up -/

/-- Carry `y` up. State: `above`, the current row `rev.reverse ++ done` scanned right to
left (`done` holds the entries already passed, all `≥ y`), and `below`. Returns the
tableau and the value pushed out of the top row. Measure `(above.length, rev.length)`,
mirroring `go`. -/
def up (y : Nat) : Tab → Row → Row → Tab → Tab × Nat
  | _, [], done, below => (done :: below, y)            -- does not occur for valid input
  | above, z :: zs, done, below =>
    if z < y then                                        -- y replaces z, and z moves up
      match above with
      | [] => ((zs.reverse ++ y :: done) :: below, z)
      | a :: as => up z as a.reverse [] ((zs.reverse ++ y :: done) :: below)
    else up y above zs (z :: done) below                 -- move left along the row
termination_by above rev => (above.length, rev.length)
decreasing_by all_goals (simp_wf; simp [Prod.lex_def]; try omega)

/-- `x` has just left the row at the top of `cur`; carry it up through `above`. (No recursion.) -/
def climb (x : Nat) (above cur : Tab) : Tab × Nat :=
  match above with
  | [] => (cur, x)
  | a :: as => up x as a.reverse [] cur

/-- Remove the last box of row `i`, then climb. -/
def unins (i : Nat) (t : Tab) : Tab × Nat :=
  let r := t.getD i []
  climb (r.getLast?.getD 0) (t.take i).reverse (mk r.dropLast (t.drop (i + 1)))

/-! ## Proofs -/

/-- One `up` step that replaces an entry is one `climb`. -/
theorem up_hit (y z : Nat) (above : Tab) (zs done : Row) (below : Tab) (h : z < y) :
    up y above (z :: zs) done below = climb z above ((zs.reverse ++ y :: done) :: below) := by
  cases above <;> simp [up, climb, h]

/-- The skip steps of `up` move past the entries `≥ y` (induction following `up`'s skip case). -/
theorem up_scan (x y : Nat) (above : Tab) (pre : Row) (below : Tab) (hxy : x < y) :
    ∀ (zs done : Row), (∀ b ∈ zs, y ≤ b) →
    up y above (zs ++ x :: pre) done below
      = climb x above ((pre.reverse ++ y :: (zs.reverse ++ done)) :: below)
  | [], done, _ => by simpa using up_hit y x above pre done below hxy
  | z :: zs, done, hz => by
    have : ¬ z < y := by have := hz z (by simp); omega
    have e : up y above (z :: (zs ++ x :: pre)) done below
        = up y above (zs ++ x :: pre) (z :: done) below := by
      rw [up.eq_def]; simp [this]
    rw [List.cons_append, e, up_scan x y above pre below hxy zs (z :: done) (fun b hb => hz b (by simp [hb]))]
    simp

theorem drop_mid (l₁ : Tab) (a : Row) (l₂ : Tab) : (l₁ ++ a :: l₂).drop (l₁.length + 1) = l₂ := by
  induction l₁ <;> simp_all

/-- THE MAIN PROOF: one recursion with `go`'s measure. Every call to the
induction hypothesis is on a smaller `(below.length, row.length)`. -/
theorem unins_go (x : Nat) (above : Tab) (pre : Row) : ∀ (row : Row) (below : Tab),
    Sorted row → (∀ p ∈ pre, p ≤ x) → Good below →
    unins (go x above pre row below).2 (go x above pre row below).1
      = climb x above (mk (pre.reverse ++ row) below)
  | [], below, _, _, _ => by
    -- x settles at the end of the row: unins finds exactly this box
    unfold go
    have hd : (above.reverse ++ (pre.reverse ++ [x]) :: below).drop (above.length + 1) = below := by
      have := drop_mid above.reverse (pre.reverse ++ [x]) below
      simpa using this
    simp [unins, hd, List.take_left', List.getD_eq_getElem?_getD]
  | y :: ys, below, hs, hpre, hb => by
    have hy : ∀ b ∈ ys, y ≤ b := (List.pairwise_cons.mp hs).1
    unfold go
    split
    · -- bump: recurse with a smaller `below`
      rename_i hxy
      have hhead : Sorted (below.headD []) := by
        cases below with
        | nil => simp [Sorted]
        | cons r rs => exact (hb r (by simp)).1
      have hmk : mk (below.headD []) below.tail = below := by
        cases below with
        | nil => simp [mk]
        | cons r rs => simp [mk, (hb r (by simp)).2]
      rw [unins_go y _ [] (below.headD []) below.tail hhead (by simp)
            (fun r h => hb r (List.mem_of_mem_tail h))]
      simp only [List.reverse_nil, List.nil_append, hmk, climb]
      -- `up` scans back across ys and lands on x
      have := up_scan x y above pre below hxy ys.reverse [] (by simpa using hy)
      simp only [List.reverse_append, List.reverse_cons, List.reverse_reverse,
        List.append_assoc, List.singleton_append, List.append_nil] at this ⊢
      rw [this]; cases above <;> simp [climb, mk]
    · -- skip: recurse with a smaller `row`
      rename_i hxy
      have ih := unins_go x above (y :: pre) ys below (List.pairwise_cons.mp hs).2
        (fun p hp => by simp at hp; rcases hp with rfl | hp; omega; exact hpre p hp) hb
      simpa using ih
termination_by row below => (below.length, row.length)
decreasing_by all_goals (simp_wf; cases below <;> simp [Prod.lex_def] <;> omega)

/-- Same recursion pattern: insertion keeps the tableau valid. -/
theorem go_good (x : Nat) (above : Tab) (pre : Row) : ∀ (row : Row) (below : Tab),
    Good above → Sorted (pre.reverse ++ row) → (∀ p ∈ pre, p ≤ x) → Good below →
    Good (go x above pre row below).1
  | [], below, ha, hs, hpre, hb => by
    unfold go
    intro r hr; simp at hr
    rcases hr with hr | rfl | hr
    · exact ha r hr
    · refine ⟨?_, by simp⟩
      simp only [List.append_nil] at hs
      exact List.pairwise_append.mpr ⟨hs, by simp, by simpa using hpre⟩
    · exact hb r hr
  | y :: ys, below, ha, hs, hpre, hb => by
    unfold go
    split
    · rename_i hxy
      have hhead : Sorted (below.headD []) := by
        cases below with
        | nil => simp [Sorted]
        | cons r rs => exact (hb r (by simp)).1
      apply go_good y _ [] (below.headD []) below.tail _ (by simpa using hhead) (by simp)
        (fun r h => hb r (List.mem_of_mem_tail h))
      intro r hr; simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · refine ⟨?_, by simp⟩
        have hs' := List.pairwise_append.mp hs
        have hyys := List.pairwise_cons.mp hs'.2.1
        refine List.pairwise_append.mpr ⟨hs'.1, ?_, ?_⟩
        · exact List.pairwise_cons.mpr
            ⟨fun b hb' => by have := hyys.1 b hb'; omega, hyys.2⟩
        · intro a ha' b hb'
          simp at hb'
          rcases hb' with rfl | hb'
          · exact hpre a (by simpa using ha')
          · exact hs'.2.2 a ha' b (by simp [hb'])
      · exact ha r hr
    · rename_i hxy
      exact go_good x above (y :: pre) ys below ha (by simpa using hs)
        (fun p hp => by simp at hp; rcases hp with rfl | hp; omega; exact hpre p hp) hb
termination_by row below => (below.length, row.length)
decreasing_by all_goals (simp_wf; cases below <;> simp [Prod.lex_def] <;> omega)

theorem unins_ins (x : Nat) (t : Tab) (h : Good t) : unins (ins x t).2 (ins x t).1 = (t, x) := by
  cases t with
  | nil => simp [ins, go, unins, climb, mk]
  | cons r rs =>
    have := unins_go x [] [] r rs (h r (by simp)).1 (by simp) (fun r' h' => h r' (by simp [h']))
    simpa [ins, mk, climb, (h r (by simp)).2] using this

theorem ins_good (x : Nat) (t : Tab) (h : Good t) : Good (ins x t).1 := by
  cases t with
  | nil => simp [ins, go, Good, Sorted]
  | cons r rs =>
    exact go_good x [] [] r rs (by simp [Good]) (by simpa using (h r (by simp)).1) (by simp)
      (fun r' h' => h r' (by simp [h']))

/-! ## RSK on words: a plain outer recursion over the word -/

/-- RSK on a word, inserting the letters from right to left. Returns the insertion tableau
and the row index of each new box (the recording data). -/
def rsk : List Nat → Tab × List Nat
  | [] => ([], [])
  | x :: w => let p := rsk w; let q := ins x p.1; (q.1, q.2 :: p.2)

/-- Inverse RSK: peel the boxes off again using the recording data. -/
def unrsk : Tab → List Nat → List Nat
  | _, [] => []
  | t, i :: is => let q := unins i t; q.2 :: unrsk q.1 is

theorem rsk_good : ∀ w, Good (rsk w).1
  | [] => by intro r hr; simp [rsk] at hr
  | x :: w => ins_good x _ (rsk_good w)

theorem unrsk_rsk : ∀ w, unrsk (rsk w).1 (rsk w).2 = w
  | [] => by simp [rsk, unrsk]
  | x :: w => by
    simp only [rsk, unrsk]
    rw [unins_ins x _ (rsk_good w)]
    simp [unrsk_rsk w]


/-! ## The other direction: `ins` undoes `unins`

The only shape facts this direction needs are that rows are sorted and the FIRST column
is strictly increasing (`Adj`). Every semistandard tableau satisfies both. -/

/-- The rows `above` (nearest first) sit correctly over the current row `R`. -/
def Col : Tab → Row → Prop
  | [], _ => True
  | a :: as, R => Sorted a ∧ Adj a R ∧ Col as a

/-- Forward skip steps: `go` moves past entries `≤ x` (induction following `go`'s skip case). -/
theorem go_scan (x : Nat) (A below : Tab) : ∀ (zs pre rest : Row), (∀ w ∈ zs, w ≤ x) →
    go x A pre (zs ++ rest) below = go x A (zs.reverse ++ pre) rest below
  | [], pre, rest, _ => by simp
  | z :: zs, pre, rest, h => by
    have hz : ¬ x < z := by have := h z (by simp); omega
    have e : go x A pre (z :: (zs ++ rest)) below = go x A (z :: pre) (zs ++ rest) below := by
      rw [go.eq_def]; simp [hz]
    rw [List.cons_append, e, go_scan x A below zs (z :: pre) rest (fun w hw => h w (by simp [hw]))]
    simp

/-- THE MAIN PROOF of this direction: one recursion with `up`'s measure
`(above.length, rev.length)`. Running `ins` on the output of `up` reaches the state
where `y` is about to go back down into `below`, with every row above restored. -/
theorem ins_up (y : Nat) : ∀ (above : Tab) (rev done : Row) (below : Tab),
    Sorted (rev.reverse ++ done) → (∃ w ∈ rev, w < y) → Col above (rev.reverse ++ done) →
    ins (up y above rev done below).2 (up y above rev done below).1
      = go y ((rev.reverse ++ done) :: above) [] (below.headD []) below.tail
  | _, [], _, _, _, ⟨w, hw, _⟩, _ => by simp at hw
  | above, z :: zs, done, below, hs, hex, hcol => by
    have hR : (z :: zs).reverse ++ done = zs.reverse ++ z :: done := by simp
    rw [hR] at hs hcol ⊢
    have hle : ∀ w ∈ zs.reverse, w ≤ z := fun w hw =>
      (List.pairwise_append.mp hs).2.2 w hw z (by simp)
    -- forward, starting where z was swapped out: skip zs.reverse, then z bumps y back down
    have fwd : ∀ A, z < y → go z A [] (zs.reverse ++ y :: done) below
        = go y ((zs.reverse ++ z :: done) :: A) [] (below.headD []) below.tail := by
      intro A hzy
      rw [go_scan z A below zs.reverse [] (y :: done) hle, go.eq_def]
      simp [hzy]
    by_cases hzy : z < y
    · -- swap: y replaces z, and z moves up
      cases above with
      | nil =>
        have e : up y [] (z :: zs) done below = ((zs.reverse ++ y :: done) :: below, z) := by
          rw [up.eq_def]; simp [hzy]
        rw [e]
        exact fwd [] hzy
      | cons a as =>
        have e : up y (a :: as) (z :: zs) done below
            = up z as a.reverse [] ((zs.reverse ++ y :: done) :: below) := by
          rw [up.eq_def]; simp [hzy]
        obtain ⟨hsa, ⟨w, hwa, hw⟩, hcol'⟩ := hcol
        rw [e, ins_up z as a.reverse [] _ (by simpa using hsa)
              ⟨w, by simpa using hwa, hw z (by simp)⟩ (by simpa using hcol')]
        simpa using fwd (a :: as) hzy
    · -- skip: move left along the row
      have e : up y above (z :: zs) done below = up y above zs (z :: done) below := by
        rw [up.eq_def]; simp [hzy]
      obtain ⟨w, hw, hwy⟩ := hex
      have hw' : w ∈ zs := by
        simp at hw; rcases hw with rfl | h
        · exact absurd hwy hzy
        · exact h
      rw [e, ins_up y above zs (z :: done) below hs ⟨w, hw', hwy⟩ hcol]
termination_by above rev => (above.length, rev.length)
decreasing_by all_goals (simp_wf; subst_vars; simp [Prod.lex_def]; try omega)

theorem ins_climb (z : Nat) (above cur : Tab) (r : Row) (hz : z ∈ r)
    (hcol : Col above r) :
    ins (climb z above cur).2 (climb z above cur).1 = go z above [] (cur.headD []) cur.tail := by
  cases above with
  | nil => rfl
  | cons a as =>
    obtain ⟨hsa, ⟨w, hwa, hw⟩, hcol'⟩ := hcol
    have := ins_up z as a.reverse [] cur (by simpa using hsa)
      ⟨w, by simpa using hwa, hw z hz⟩ (by simpa using hcol')
    simpa [climb] using this

/-- Putting the removed corner back: `z` is the largest entry of its row, so it goes at the end. -/
theorem go_corner (A B : Tab) (r0 : Row) (z : Nat) (hs : Sorted (r0 ++ [z]))
    (hB : r0 = [] → B = []) :
    go z A [] ((mk r0 B).headD []) (mk r0 B).tail = (A.reverse ++ (r0 ++ [z]) :: B, A.length) := by
  by_cases h0 : r0 = []
  · subst h0; have := hB rfl; subst this; simp [mk, go]
  · have hle : ∀ w ∈ r0, w ≤ z := fun w hw => (List.pairwise_append.mp hs).2.2 w hw z (by simp)
    have := go_scan z A B r0 [] [] hle
    simp only [List.append_nil] at this
    simp only [mk, h0, ↓reduceIte, List.headD, List.tail]
    rw [this, go.eq_def]
    simp

theorem col_take (P : Tab) (hg : Good P) (hc : ColStrict P) :
    ∀ i (hi : i < P.length), Col (P.take i).reverse P[i]
  | 0, _ => by simp [Col]
  | i + 1, hi => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    exact ⟨(hg _ (List.getElem_mem _)).1, hc i hi, col_take P hg hc i (by omega)⟩

/-- `ins` undoes `unins` at a corner of a valid tableau. -/
theorem ins_unins (P : Tab) (i : Nat) (hg : Good P)
    (hc : ColStrict P) (hi : i < P.length)
    (hcorner : ∀ h : i + 1 < P.length, P[i+1].length < P[i].length) :
    ins (unins i P).2 (unins i P).1 = (P, i) := by
  have hne : P[i] ≠ [] := (hg _ (List.getElem_mem _)).2
  obtain ⟨r0, z, hr⟩ : ∃ r0 z, P[i] = r0 ++ [z] := by
    rcases List.eq_nil_or_concat P[i] with h | ⟨L, b, h⟩
    · exact absurd h hne
    · exact ⟨L, b, by simpa using h⟩
  have hu : unins i P = climb z (P.take i).reverse (mk r0 (P.drop (i + 1))) := by
    simp [unins, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hr]
  have hcol := col_take P hg hc i hi
  rw [hr] at hcol
  rw [hu, ins_climb z _ _ (r0 ++ [z]) (by simp) hcol]
  have hs : Sorted (r0 ++ [z]) := hr ▸ (hg _ (List.getElem_mem _)).1
  have hB : r0 = [] → P.drop (i + 1) = [] := by
    intro h0
    apply List.drop_eq_nil_of_le
    refine Nat.not_lt.mp fun h => ?_
    have h1 := hcorner h
    rw [hr, h0, List.nil_append, List.length_singleton] at h1
    have : P[i+1] = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact (hg _ (List.getElem_mem _)).2 this
  rw [go_corner _ _ r0 z hs hB, List.reverse_reverse, ← hr]
  have hlen : (P.take i).reverse.length = i := by simp; omega
  rw [hlen, ← List.drop_eq_getElem_cons hi, List.take_append_drop]

/-! ## Both directions on words -/

/-- **Inverse RSK after RSK is the identity** on recording data that can be peeled off. -/
theorem rsk_unrsk : ∀ (is : List Nat) (t : Tab), Valid unins t is → rsk (unrsk t is) = (t, is)
  | [], t, h => by simp [Valid] at h; subst h; simp [unrsk, rsk]
  | i :: is, t, ⟨hg, hc, ⟨hi, hcorner⟩, hv⟩ => by
    simp only [unrsk, rsk]
    rw [rsk_unrsk is _ hv, ins_unins t i hg hc hi hcorner]

end RMT.RSK.Zipper
