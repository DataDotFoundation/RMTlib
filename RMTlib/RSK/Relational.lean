import RMTlib.RSK.Insert

/-!
# RSK by bumping, as inductive relations

Row insertion, tableau insertion and RSK on words, each stated as an inductive predicate
whose constructors are the steps of the bumping algorithm:

* `RowIns x r r' b`: inserting `x` into row `r` gives row `r'` and bumps `b`.
* `Ins x t t' i`: inserting `x` into tableau `t` gives `t'`, and the new box is in row `i`.
* `RSK w t is`: inserting the word `w` from right to left gives `t` and recording data `is`.

## The recursion scheme and what it costs

There is no function, so there is no termination question and no recursion scheme to pick:
each relation is an inductive family, and every proof is a rule induction on a derivation.

What this buys is a direct statement of invertibility. Inversion is not a second algorithm
here. It is the claim that the converse relation is functional: the output tableau and the
recording index determine the inserted value and the old tableau (`ins_inj`). The proof is
one rule induction on the first derivation, with a case split on the last rule of the
second. It never mentions uninsertion. Its only inputs are three facts about a single
derivation (the inserted value appears in the output, a bumped value is larger, the output
is nonempty) and sorted, nonempty rows (`Good`). It does not need the first column to be
strictly increasing, which `Nested.unins_ins` does not need either but `Nested.ins_unins`
does.

Compare `Nested.unrsk_rsk`. It proves injectivity by exhibiting an inverse function
`Nested.unrsk`, and that proof needs both `unrsk` and the row-level inverse
`rowUnins`. Here injectivity (`rsk_inj`) needs no inverse function. The price is that it gives
no way to compute the word from `(P, is)`: injectivity is a uniqueness statement, not a
construction.

The other direction, surjectivity onto semistandard tableaux with corner sequences, is an
existence statement, and rule induction alone does not produce the witness. We take it from
the functional world: `Nested.unins` supplies the predecessor, `Nested.ins_unins` and
`Nested.unins_ssyt` show it works, and the bridge `ins_iff` moves the result here (`ins_surj`,
`rsk_surj`). So the relational style halves the work for injectivity and does nothing for
existence.

The relations are also deterministic and total. Determinism has a direct rule-induction
proof (`ins_det`). Totality is an existence statement too, and comes from the bridge to
`Nested.ins`.

## Main results

* `rowIns_iff`, `ins_iff`, `rsk_iff`: the relations are the graphs of `Nested.rowIns`,
  `Nested.ins` and `Nested.rsk`.
* `rowIns_det`, `ins_det`, `rsk_det`: determinism, by rule induction.
* `ins_total`, `rsk_total`: totality, from the bridge.
* `rowIns_inj`, `ins_inj`: the converse relations are functional on sorted rows and `Good`
  tableaux, by rule induction, without uninsertion.
* `rsk_inj`: `(P, is)` determines the word.
* `ins_surj`, `rsk_surj`: every semistandard tableau with a corner (or a corner sequence)
  has a preimage, using `Nested.unins` as the witness.
-/

namespace RMT.RSK.Relational

open RMT.RSK

/-! ## The relations -/

/-- `RowIns x r r' b`: inserting `x` into the row `r` gives the row `r'`. The first entry
`> x` is replaced by `x` and bumped (`b = some y`); if there is none, `x` is appended
(`b = none`). -/
inductive RowIns (x : Nat) : Row → Row → Option Nat → Prop
  /-- Reaching the end of the row: append `x`, bump nothing. -/
  | nil : RowIns x [] [x] none
  /-- The current entry `y` is larger than `x`: `x` replaces it and `y` is bumped. -/
  | bump {y : Nat} {ys : Row} : x < y → RowIns x (y :: ys) (x :: ys) (some y)
  /-- The current entry `y` is at most `x`: keep it and continue along the row. -/
  | skip {y : Nat} {ys ys' : Row} {b : Option Nat} :
      ¬ x < y → RowIns x ys ys' b → RowIns x (y :: ys) (y :: ys') b

/-- `Ins x t t' i`: inserting `x` into the tableau `t` gives `t'`, and the new box is in
row `i`. A value bumped out of a row is inserted into the rows below. -/
inductive Ins : Nat → Tab → Tab → Nat → Prop
  /-- Below the last row: start a new row `[x]`. -/
  | nil (x : Nat) : Ins x [] [[x]] 0
  /-- Nothing is bumped out of the top row: the box is added there. -/
  | stop {x : Nat} {r r' : Row} {rs : Tab} : RowIns x r r' none → Ins x (r :: rs) (r' :: rs) 0
  /-- `y` is bumped out of the top row and inserted into the rows below. -/
  | bump {x y i : Nat} {r r' : Row} {rs rs' : Tab} :
      RowIns x r r' (some y) → Ins y rs rs' i → Ins x (r :: rs) (r' :: rs') (i + 1)

/-- `RSK w t is`: inserting the letters of `w` from right to left into the empty tableau gives
`t`, with `is` the row index of each new box (the last letter's index last). -/
inductive RSK : List Nat → Tab → List Nat → Prop
  /-- The empty word gives the empty tableau. -/
  | nil : RSK [] [] []
  /-- Insert the first letter into the tableau of the rest of the word. -/
  | cons {x i : Nat} {w is : List Nat} {t t' : Tab} :
      RSK w t is → Ins x t t' i → RSK (x :: w) t' (i :: is)

/-- A derivation, built by hand: `2` passes `1`, bumps `3`, which bumps `4`, which starts a
new row. -/
example : Ins 2 [[1, 3], [4]] [[1, 2], [3], [4]] 2 :=
  .bump (.skip (by decide) (.bump (by decide))) (.bump (.bump (by decide)) (.nil 4))

/-! ## The relations are the graphs of the nested functions -/

theorem rowIns_iff {x : Nat} {r r' : Row} {b : Option Nat} :
    RowIns x r r' b ↔ Nested.rowIns x r = (r', b) := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | bump hxy => simp [Nested.rowIns, hxy]
    | skip hxy _ ih => simp [Nested.rowIns, hxy, ih]
  · induction r generalizing r' b with
    | nil => intro h; simp [Nested.rowIns] at h; obtain ⟨rfl, rfl⟩ := h; exact .nil
    | cons y ys ih =>
      intro h
      unfold Nested.rowIns at h
      split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; exact .bump ‹_›
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .skip ‹_› (ih rfl)

theorem ins_iff {x : Nat} {t t' : Tab} {i : Nat} : Ins x t t' i ↔ Nested.ins x t = (t', i) := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | stop hr => simp [Nested.ins, rowIns_iff.mp hr]
    | bump hr _ ih => simp [Nested.ins, rowIns_iff.mp hr, ih]
  · induction t generalizing x t' i with
    | nil => intro h; simp [Nested.ins] at h; obtain ⟨rfl, rfl⟩ := h; exact .nil x
    | cons r rs ih =>
      intro h
      unfold Nested.ins at h
      cases hrow : Nested.rowIns x r with
      | mk r' b =>
        cases b with
        | none =>
          simp only [hrow, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .stop (rowIns_iff.mpr hrow)
        | some y =>
          simp only [hrow, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .bump (rowIns_iff.mpr hrow) (ih rfl)

theorem rsk_iff {w : List Nat} {t : Tab} {is : List Nat} :
    RSK w t is ↔ Nested.rsk w = (t, is) := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons _ hi ih => simp [Nested.rsk, ih, ins_iff.mp hi]
  · induction w generalizing t is with
    | nil => intro h; simp [Nested.rsk] at h; obtain ⟨rfl, rfl⟩ := h; exact .nil
    | cons x w ih =>
      intro h
      simp only [Nested.rsk, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .cons (ih rfl) (ins_iff.mpr rfl)

/-- Every tableau can be inserted into. -/
theorem ins_total (x : Nat) (t : Tab) : ∃ t' i, Ins x t t' i :=
  ⟨_, _, ins_iff.mpr rfl⟩

/-- Every word has an RSK image. -/
theorem rsk_total (w : List Nat) : ∃ t is, RSK w t is :=
  ⟨_, _, rsk_iff.mpr rfl⟩

/-! ## Determinism, by rule induction -/

theorem rowIns_det {x : Nat} {r r₁ r₂ : Row} {b₁ b₂ : Option Nat}
    (h₁ : RowIns x r r₁ b₁) (h₂ : RowIns x r r₂ b₂) : r₁ = r₂ ∧ b₁ = b₂ := by
  induction h₁ generalizing r₂ b₂ with
  | nil => cases h₂; exact ⟨rfl, rfl⟩
  | bump hxy =>
    cases h₂ with
    | bump => exact ⟨rfl, rfl⟩
    | skip hn _ => exact absurd hxy hn
  | skip hn _ ih =>
    cases h₂ with
    | bump hxy => exact absurd hxy hn
    | skip _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩

theorem ins_det {x : Nat} {t t₁ t₂ : Tab} {i₁ i₂ : Nat}
    (h₁ : Ins x t t₁ i₁) (h₂ : Ins x t t₂ i₂) : t₁ = t₂ ∧ i₁ = i₂ := by
  induction h₁ generalizing t₂ i₂ with
  | nil => cases h₂; exact ⟨rfl, rfl⟩
  | stop hr =>
    cases h₂ with
    | stop hr' => obtain ⟨rfl, -⟩ := rowIns_det hr hr'; exact ⟨rfl, rfl⟩
    | bump hr' _ => exact absurd (rowIns_det hr hr').2 (by simp)
  | bump hr _ ih =>
    cases h₂ with
    | stop hr' => exact absurd (rowIns_det hr hr').2 (by simp)
    | bump hr' h =>
      obtain ⟨rfl, hy⟩ := rowIns_det hr hr'
      cases hy
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩

theorem rsk_det {w : List Nat} {t₁ t₂ : Tab} {is₁ is₂ : List Nat}
    (h₁ : RSK w t₁ is₁) (h₂ : RSK w t₂ is₂) : t₁ = t₂ ∧ is₁ = is₂ := by
  induction h₁ generalizing t₂ is₂ with
  | nil => cases h₂; exact ⟨rfl, rfl⟩
  | cons _ hi ih =>
    cases h₂ with
    | cons h hi' =>
      obtain ⟨rfl, rfl⟩ := ih h
      obtain ⟨rfl, rfl⟩ := ins_det hi hi'
      exact ⟨rfl, rfl⟩

/-! ## Facts about one row derivation -/

theorem RowIns.mem_out {x : Nat} {r r' : Row} {b : Option Nat} (h : RowIns x r r' b) : x ∈ r' := by
  induction h with
  | nil => simp
  | bump => simp
  | skip _ _ ih => exact List.mem_cons_of_mem _ ih

theorem RowIns.ne_nil {x : Nat} {r r' : Row} {b : Option Nat} (h : RowIns x r r' b) : r' ≠ [] := by
  cases h <;> simp

theorem RowIns.bump_gt {x y : Nat} {r r' : Row} (h : RowIns x r r' (some y)) : x < y := by
  generalize hb : some y = b at h
  induction h with
  | nil => cases hb
  | bump hxy => cases hb; exact hxy
  | skip _ _ ih => exact ih hb

theorem RowIns.mem_cases {x : Nat} {r r' : Row} {b : Option Nat} (h : RowIns x r r' b) :
    ∀ v ∈ r', v = x ∨ v ∈ r := by
  induction h with
  | nil => simp
  | bump => intro v hv; simp at hv; rcases hv with h | h <;> simp [h]
  | skip _ _ ih =>
    intro v hv; simp at hv
    rcases hv with h | h
    · simp [h]
    · rcases ih v h with h' | h' <;> simp [h']

theorem RowIns.sorted {x : Nat} {r r' : Row} {b : Option Nat} (h : RowIns x r r' b)
    (hs : Sorted r) : Sorted r' := by
  induction h with
  | nil => simp [Sorted]
  | bump hxy =>
    have hz := (List.pairwise_cons.mp hs).1
    exact List.pairwise_cons.mpr ⟨fun v hv => Nat.le_trans (Nat.le_of_lt hxy) (hz v hv),
      (List.pairwise_cons.mp hs).2⟩
  | skip hn h ih =>
    have hz := (List.pairwise_cons.mp hs).1
    refine List.pairwise_cons.mpr ⟨fun v hv => ?_, ih (List.pairwise_cons.mp hs).2⟩
    rcases h.mem_cases v hv with rfl | hv
    · omega
    · exact hz v hv

/-- A row derivation with nothing bumped and a one-box output started from the empty row. -/
theorem RowIns.single {x z : Nat} {r : Row} (h : RowIns x r [z] none) : r = [] := by
  cases h with
  | nil => rfl
  | skip _ h' => exact absurd rfl h'.ne_nil

theorem Ins.good {x : Nat} {t t' : Tab} {i : Nat} (h : Ins x t t' i) (hg : Good t) : Good t' := by
  induction h with
  | nil => intro r hr; simp at hr; subst hr; simp [Sorted]
  | stop hr =>
    intro s hs; simp at hs
    rcases hs with rfl | hs
    · exact ⟨hr.sorted (hg _ (by simp)).1, hr.ne_nil⟩
    · exact hg s (by simp [hs])
  | bump hr _ ih =>
    intro s hs; simp at hs
    rcases hs with rfl | hs
    · exact ⟨hr.sorted (hg _ (by simp)).1, hr.ne_nil⟩
    · exact ih hg.tail s hs

theorem RSK.good {w : List Nat} {t : Tab} {is : List Nat} (h : RSK w t is) : Good t := by
  induction h with
  | nil => intro r hr; simp at hr
  | cons _ hi ih => exact hi.good ih

/-! ## Injectivity: the converse relations are functional -/

/-- **Row level.** On sorted rows, the output row and the bumped value determine the inserted
value and the old row. Rule induction on the first derivation. -/
theorem rowIns_inj {x x' : Nat} {r s r' : Row} {b : Option Nat}
    (h : RowIns x r r' b) (h' : RowIns x' s r' b) (hr : Sorted r) (hs : Sorted s) :
    x = x' ∧ r = s := by
  induction h generalizing x' s with
  | nil =>
    cases h' with
    | nil => exact ⟨rfl, rfl⟩
    | skip _ h'' => exact absurd rfl h''.ne_nil
  | bump hxy =>
    cases h' with
    | bump => exact ⟨rfl, rfl⟩
    | skip hn h'' =>
      -- `x'` lands among the entries after the bumped `y`, which are all `≥ y > x'`
      exact absurd ((List.pairwise_cons.mp hr).1 _ h''.mem_out) (Nat.not_le.mpr h''.bump_gt)
  | skip hn h₁ ih =>
    cases h' with
    | nil => exact absurd rfl h₁.ne_nil
    | bump hxy =>
      -- symmetric: `x` lands among entries `≥ z > x`
      exact absurd ((List.pairwise_cons.mp hs).1 _ h₁.mem_out) (Nat.not_le.mpr h₁.bump_gt)
    | skip _ h'' =>
      obtain ⟨rfl, rfl⟩ := ih h'' (List.pairwise_cons.mp hr).2 (List.pairwise_cons.mp hs).2
      exact ⟨rfl, rfl⟩

/-- **Tableau level.** On `Good` tableaux, the output tableau and the recording index
determine the inserted value and the old tableau. Rule induction on the first derivation;
no uninsertion function is used. -/
theorem ins_inj {x x' : Nat} {t s t' : Tab} {i : Nat}
    (h : Ins x t t' i) (h' : Ins x' s t' i) (ht : Good t) (hs : Good s) :
    x = x' ∧ t = s := by
  induction h generalizing x' s with
  | nil =>
    cases h' with
    | nil => exact ⟨rfl, rfl⟩
    | stop hr => exact absurd hr.single (hs _ (by simp)).2
  | stop hr =>
    cases h' with
    | nil => exact absurd hr.single (ht _ (by simp)).2
    | stop hr' =>
      obtain ⟨rfl, rfl⟩ := rowIns_inj hr hr' (ht _ (by simp)).1 (hs _ (by simp)).1
      exact ⟨rfl, rfl⟩
  | bump hr _ ih =>
    cases h' with
    | bump hr' h'' =>
      -- the rows below determine the bumped value, then the top row determines the rest
      obtain ⟨rfl, rfl⟩ := ih h'' ht.tail hs.tail
      obtain ⟨rfl, rfl⟩ := rowIns_inj hr hr' (ht _ (by simp)).1 (hs _ (by simp)).1
      exact ⟨rfl, rfl⟩

/-- **RSK is injective**: the tableau and the recording data determine the word. Compare
`Nested.unrsk_rsk`, which proves the same by exhibiting an inverse function. -/
theorem rsk_inj {w w' : List Nat} {t : Tab} {is : List Nat}
    (h : RSK w t is) (h' : RSK w' t is) : w = w' := by
  induction h generalizing w' with
  | nil => cases h'; rfl
  | cons h₀ hi ih =>
    cases h' with
    | cons h₀' hi' =>
      obtain ⟨rfl, rfl⟩ := ins_inj hi hi' h₀.good h₀'.good
      rw [ih h₀']

/-! ## Surjectivity: existence needs a witness -/

/-- Every semistandard tableau with a corner in row `i` comes from inserting some value into
a semistandard tableau. The witness is `Nested.unins i t`. With `ins_inj`, this predecessor
is unique among `Good` tableaux. -/
theorem ins_surj {t : Tab} {i : Nat} (hss : SSYT t) (hc : Corner i t) :
    ∃ x s, SSYT s ∧ Ins x s t i :=
  ⟨_, _, (Nested.unins_ssyt i t hss hc).1,
    ins_iff.mpr (Nested.ins_unins i t hss.good hss.colStrict hc)⟩

/-- Every semistandard tableau with a sequence of corners is the RSK image of some word. The
witness is `Nested.unrsk t is`. -/
theorem rsk_surj {t : Tab} {is : List Nat} (hss : SSYT t) (hp : Peelable Nested.unins t is) :
    ∃ w, RSK w t is :=
  ⟨_, rsk_iff.mpr (Nested.rsk_unrsk_ssyt is t hss hp)⟩

end RMT.RSK.Relational
