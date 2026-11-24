import RMTlib.RSK.Insert

/-!
# RSK with the invariants in the types

The other bumping modules are extrinsic: a tableau is a plain list of rows, and each theorem
carries side conditions (`Good`, `SSYT`, `Corner`, `Valid`, `Peelable`). This module moves
those conditions into the types, so that the final statements have no hypotheses.

* `SSYTab` is a list of rows together with a proof that it is semistandard.
* `Cor T` is a row index together with a proof that it is a corner of `T`.
* `insert x T` returns a new `SSYTab` and the corner where it grew. `uninsert T c` takes a
  corner, so it cannot be called at a bad index.

The missing piece was `ins_corner`: the recording index returned by insertion is a corner of
the new tableau. With it, `rsk_peelable` says the recording data of `rsk w` is peelable. So
the image of `Nested.rsk` is now characterised: exactly the semistandard tableaux with
peelable recording data. Two encodings of the recording data are compared.

1. A subtype. `RSKOut n` is the set of pairs `(P, is)` with `P` semistandard, `is` peelable,
   and `is.length = n`. `rskEquiv n` is an equivalence between words of length `n` and
   `RSKOut n`. The maps are `Nested.rsk` and `Nested.unrsk` with proofs attached.
2. An indexed family. `Rec T` is a certificate that `T` peels down to the empty tableau: each
   `peel` names a corner and a certificate for what is left. `unrskR` is structural
   recursion on the certificate, not on the list, and never checks a corner. `rskEquivR` is
   an equivalence between all words and `Σ T, Rec T`; no length index is needed.

`Rec.ofPeelable`, `Rec.toList` and their round trips show the two encodings carry the same
data, and `unrskR_eq`, `rskR_eq` show the intrinsic functions compute the extrinsic ones.

## The recursion scheme and what it costs

The recursions are those of `RMT.RSK.Nested`, unchanged. Insertion and uninsertion on
`SSYTab` call `Nested.ins` and `Nested.unins` on the rows and attach `ins_ssyt`,
`ins_corner` or `unins_ssyt`. `rskR` and `unrskR` are structural recursions on the word and
on the certificate. Every invariant proof is still an extrinsic theorem; the types only
package them.

What it buys.
* The final statements are hypothesis-free: `uninsert_insert`, `insert_uninsert`,
  `rskEquiv`, `rskEquivR`. Compare `Nested.rsk_unrsk_ssyt`, which takes `SSYT` and `Peelable`.
* Bad input cannot be written down: `uninsert` needs a `Cor T`, and `unrskR` needs a `Rec T`.
* `Valid` and `Peelable` disappear from the user statements: they are threaded once, inside
  `rskOut`, `Rec` and `Rec.ofPeelable`.

What it costs.
* Proof terms live inside definitions. `insert` needs `ins_corner`, a new induction, before
  it can even be stated with an intrinsic corner.
* Equality needs bookkeeping. `SSYTab.ext'` and `Subtype.ext` reduce equality to the rows by
  proof irrelevance. `insert_uninsert` is an equation in a sigma type, so it needs
  `sigma_ext`: compare rows, substitute, then compare indices.
* Dependent rewriting fails. In `rskR_unrskR`, `rw` with the induction hypothesis inside the
  certificate first failed with "motive is not type correct": Lean had abstracted the proof
  in `rskR` into an auxiliary lemma about `unrskR rest`, not about `rskR (unrskR rest)`. The
  fix is to route the step through `growR`, whose proof depends only on its argument, and to
  state `peel_eq` for an arbitrary sigma value `g` and an arbitrary proof `hg`, so that the
  equation `g = ⟨T, c⟩` can be substituted.
* The shape of `Rec` matters. With the computed index `peel (rest : Rec (uninsert T c).1)`,
  `rskR` would have to cast the old certificate along `uninsert_insert`. Instead `Rec` takes
  the tableau below as a field with an equation (both constructors return `Rec T` for a
  variable `T`). Then no cast appears in data and pattern matching on `Rec T` never gets stuck.
* Structural recursion breaks through `subst`. In a proof by recursion on `Rec`, the
  recursive call must be made before `subst h`; after it, Lean no longer sees the call as
  structural.
* `decide` partly survives. It evaluates the lists projected out of `rskOut` and `rskR`, and
  `unrskOut (rskOut w) = w` for concrete `w`, because proof fields are never evaluated. But
  `SSYT` and `Corner` have no `Decidable` instance, so a concrete `SSYTab` or `RSKOut` value
  needs a hand proof (`simp` works, see the examples at the end), and `Σ T, Rec T` has no
  decidable equality.

## Main results

* `ins_corner`: after inserting into a semistandard tableau, the recording index is a corner.
* `rsk_peelable`: the recording data of `Nested.rsk w` is peelable.
* `uninsert_insert`, `insert_uninsert`: insertion on `SSYTab` is inverted by uninsertion at a
  corner, with no hypotheses.
* `rskEquiv`: RSK is an equivalence between words of length `n` and `RSKOut n`.
* `rskEquivR`: RSK is an equivalence between words and tableaux with a certificate `Rec T`.
* `Rec.toList_ofPeelable`, `Rec.ofPeelable_toList`: certificates are peelable lists.
-/

namespace RMT.RSK.Intrinsic

open RMT.RSK

/-! ## The corner lemma and the image of `rsk` -/

/-- A corner of the rows below is a corner one row further down of the whole tableau. -/
theorem corner_cons {i : Nat} {r : Row} {rs : Tab} (h : Corner i rs) :
    Corner (i + 1) (r :: rs) := by
  obtain ⟨hi, hc⟩ := h
  exact ⟨by simp; omega, fun h' => by simpa using hc (by simp at h'; omega)⟩

/-- **The recording index is a corner.** After inserting into a semistandard tableau, the row
that gained a box ends in a corner of the new tableau. Induction following `Nested.ins`. -/
theorem ins_corner (x : Nat) : ∀ (t : Tab), SSYT t →
    Corner (Nested.ins x t).2 (Nested.ins x t).1
  | [], _ => ⟨by simp [Nested.ins], fun h => by simp [Nested.ins] at h⟩
  | r :: rs, hss => by
    unfold Nested.ins
    cases hrow : Nested.rowIns x r with
    | mk r' b =>
      cases b with
      | none =>
        have happ : r' = r ++ [x] := by
          simpa [hrow] using Nested.rowIns_none x r (by simp [hrow])
        subst happ
        refine ⟨by simp, fun h => ?_⟩
        cases rs with
        | nil => simp at h
        | cons s ss => have := hss.2.1.1; simp; omega
      | some y => exact corner_cons (ins_corner y rs hss.tail)

/-- The recording data of `rsk w` can be peeled off its insertion tableau, each index a corner
when it is used. -/
theorem rsk_peelable : ∀ w, Peelable Nested.unins (Nested.rsk w).1 (Nested.rsk w).2
  | [] => rfl
  | x :: w => by
    refine ⟨ins_corner x _ (Nested.rsk_ssyt w), ?_⟩
    show Peelable _ (Nested.unins (Nested.ins x (Nested.rsk w).1).2
      (Nested.ins x (Nested.rsk w).1).1).1 _
    rw [Nested.unins_ins x _ (Nested.rsk_ssyt w).good]
    exact rsk_peelable w

/-- RSK records one index per letter. -/
theorem rsk_length : ∀ w, (Nested.rsk w).2.length = w.length
  | [] => rfl
  | x :: w => by simp [Nested.rsk, rsk_length w]

/-- Inverse RSK returns one letter per index. -/
theorem unrsk_length (t : Tab) (is : List Nat) : (Nested.unrsk t is).length = is.length := by
  induction is generalizing t with
  | nil => rfl
  | cons i is ih => simp [Nested.unrsk, ih]

/-! ## Semistandard tableaux as a type -/

/-- A semistandard Young tableau: its rows together with a proof that they are semistandard. -/
structure SSYTab where
  /-- The rows, top to bottom. -/
  rows : Tab
  /-- The rows form a semistandard tableau. -/
  ssyt : SSYT rows

/-- Two semistandard tableaux are equal when their rows are: the proof field is irrelevant. -/
theorem SSYTab.ext' {T T' : SSYTab} (h : T.rows = T'.rows) : T = T' := by
  cases T; cases T'; cases h; rfl

/-- The empty tableau. -/
def SSYTab.empty : SSYTab := ⟨[], fun _ h => by simp at h, trivial⟩

/-- A corner of `T`: a row index whose last box can be removed. -/
abbrev Cor (T : SSYTab) := {i : Nat // Corner i T.rows}

/-- Insert `x`. The result is a semistandard tableau together with the corner where it grew. -/
def insert (x : Nat) (T : SSYTab) : Σ T' : SSYTab, Cor T' :=
  ⟨⟨(Nested.ins x T.rows).1, (Nested.ins_ssyt x T.rows T.ssyt).1⟩,
    ⟨(Nested.ins x T.rows).2, ins_corner x T.rows T.ssyt⟩⟩

/-- Uninsert at a corner. It cannot be called at an index that is not a corner. -/
def uninsert (T : SSYTab) (c : Cor T) : SSYTab × Nat :=
  (⟨(Nested.unins c.1 T.rows).1, (Nested.unins_ssyt c.1 T.rows T.ssyt c.2).1⟩,
    (Nested.unins c.1 T.rows).2)

/-- Uninsertion undoes insertion. No hypothesis. -/
theorem uninsert_insert (x : Nat) (T : SSYTab) :
    uninsert (insert x T).1 (insert x T).2 = (T, x) := by
  have h := Nested.unins_ins x T.rows T.ssyt.good
  have h2 : (Nested.unins (Nested.ins x T.rows).2 (Nested.ins x T.rows).1).2 = x :=
    congrArg Prod.snd h
  exact Prod.ext (SSYTab.ext' (congrArg Prod.fst h)) h2

/-- Equality in `Σ T, Cor T` reduces to equality of the rows and of the indices. -/
theorem sigma_ext {T T' : SSYTab} {c : Cor T} {c' : Cor T'} (h : T.rows = T'.rows)
    (hc : c.1 = c'.1) : (⟨T, c⟩ : Σ T, Cor T) = ⟨T', c'⟩ := by
  cases SSYTab.ext' h
  obtain ⟨i, _⟩ := c
  obtain ⟨i', _⟩ := c'
  cases hc
  rfl

/-- Insertion undoes uninsertion, and returns the same corner. No hypothesis. -/
theorem insert_uninsert (T : SSYTab) (c : Cor T) :
    insert (uninsert T c).2 (uninsert T c).1 = ⟨T, c⟩ := by
  have h := Nested.ins_unins c.1 T.rows T.ssyt.good T.ssyt.colStrict c.2
  exact sigma_ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-! ## Encoding 1: a subtype of outputs, and a hypothesis-free equivalence -/

/-- A minimal equivalence of types: two maps, inverse to each other. -/
structure Equiv (α β : Type) where
  /-- The forward map. -/
  toFun : α → β
  /-- The backward map. -/
  invFun : β → α
  /-- Backward after forward is the identity. -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- Forward after backward is the identity. -/
  right_inv : ∀ b, toFun (invFun b) = b

/-- Words of length `n`. -/
abbrev Word (n : Nat) := {w : List Nat // w.length = n}

/-- The possible outputs of RSK on words of length `n`: a semistandard tableau and `n` recording
indices that peel it, one corner at a time, down to the empty tableau. -/
abbrev RSKOut (n : Nat) :=
  {p : Tab × List Nat // SSYT p.1 ∧ Peelable Nested.unins p.1 p.2 ∧ p.2.length = n}

/-- RSK, landing in `RSKOut n`. -/
def rskOut {n : Nat} (w : Word n) : RSKOut n :=
  ⟨Nested.rsk w.1, Nested.rsk_ssyt w.1, rsk_peelable w.1, (rsk_length w.1).trans w.2⟩

/-- Inverse RSK, defined on all of `RSKOut n`. -/
def unrskOut {n : Nat} (p : RSKOut n) : Word n :=
  ⟨Nested.unrsk p.1.1 p.1.2, (unrsk_length _ _).trans p.2.2.2⟩

/-- **RSK is a bijection** from words of length `n` onto semistandard tableaux with peelable
recording data of length `n`. Neither round trip has a hypothesis. -/
def rskEquiv (n : Nat) : Equiv (Word n) (RSKOut n) where
  toFun := rskOut
  invFun := unrskOut
  left_inv w := Subtype.ext (Nested.unrsk_rsk w.1)
  right_inv p := Subtype.ext (Nested.rsk_unrsk_ssyt p.1.2 p.1.1 p.2.1 p.2.2.1)

/-! ## Encoding 2: the recording data as an indexed family -/

/-- A certificate that `T` can be peeled down to the empty tableau. Each `peel` names a corner
and the certificate for what is left. The tableau below is a field, with an equation, rather
than an index computed from `T` (`Rec (uninsert T c).1`): with the computed index, building a
certificate after an insertion needs a cast along `uninsert_insert`. -/
inductive Rec : SSYTab → Type where
  /-- The empty tableau needs no more peeling. -/
  | nil (T : SSYTab) (h : T.rows = []) : Rec T
  /-- Remove the box at corner `c`, leaving `T'`, then peel `T'`. -/
  | peel (T : SSYTab) (c : Cor T) (T' : SSYTab) (h : (uninsert T c).1 = T') (rest : Rec T') :
      Rec T

/-- The row indices recorded in a certificate. -/
def Rec.toList : {T : SSYTab} → Rec T → List Nat
  | _, .nil _ _ => []
  | _, .peel _ c _ _ rest => c.1 :: rest.toList

/-- Inverse RSK, structurally recursive on the certificate. No corner check is needed. -/
def unrskR : {T : SSYTab} → Rec T → List Nat
  | _, .nil _ _ => []
  | _, .peel T c _ _ rest => (uninsert T c).2 :: unrskR rest

/-- One step of RSK: insert `x`, and extend the certificate by the new corner. -/
def growR (x : Nat) (p : Σ T : SSYTab, Rec T) : Σ T : SSYTab, Rec T :=
  ⟨(insert x p.1).1,
    .peel (insert x p.1).1 (insert x p.1).2 p.1 (congrArg Prod.fst (uninsert_insert x p.1)) p.2⟩

/-- RSK, returning the tableau and its certificate. -/
def rskR : List Nat → Σ T : SSYTab, Rec T
  | [] => ⟨SSYTab.empty, .nil _ rfl⟩
  | x :: w => growR x (rskR w)

/-- Inverse RSK after RSK is the identity. -/
theorem unrskR_rskR : ∀ w, unrskR (rskR w).2 = w
  | [] => rfl
  | x :: w => by
    show (uninsert (insert x (rskR w).1).1 (insert x (rskR w).1).2).2 :: unrskR (rskR w).2
      = x :: w
    rw [uninsert_insert, unrskR_rskR w]

/-- The bookkeeping step for `rskR_unrskR`: once the inserted tableau and corner are known to
be `⟨T, c⟩`, the two `peel` certificates agree by proof irrelevance. Stated for an arbitrary
`g` and proof `hg` so that the equation can be substituted. -/
theorem peel_eq {T' : SSYTab} (rest : Rec T') (g : Σ T, Cor T) (hg : (uninsert g.1 g.2).1 = T')
    (T : SSYTab) (c : Cor T) (h : (uninsert T c).1 = T') (e : g = ⟨T, c⟩) :
    (⟨g.1, .peel g.1 g.2 T' hg rest⟩ : Σ T, Rec T) = ⟨T, .peel T c T' h rest⟩ := by
  subst e; rfl

/-- RSK after inverse RSK is the identity, on every certificate. -/
theorem rskR_unrskR : ∀ {T : SSYTab} (r : Rec T), rskR (unrskR r) = ⟨T, r⟩
  | T, .nil _ h => by
    cases SSYTab.ext' (T := T) (T' := SSYTab.empty) h
    rfl
  | _, .peel T c T' h rest => by
    have ih := rskR_unrskR rest
    subst h
    show growR _ (rskR (unrskR rest)) = _
    rw [ih]
    exact peel_eq rest _ _ T c rfl (insert_uninsert T c)

/-- **RSK is a bijection** from words onto tableaux with a peeling certificate. -/
def rskEquivR : Equiv (List Nat) (Σ T : SSYTab, Rec T) where
  toFun := rskR
  invFun p := unrskR p.2
  left_inv := unrskR_rskR
  right_inv p := rskR_unrskR p.2

/-! ## The two encodings describe the same data -/

/-- A certificate gives peelable recording data. -/
theorem Rec.peelable : ∀ {T : SSYTab} (r : Rec T), Peelable Nested.unins T.rows r.toList
  | _, .nil _ h => h
  | _, .peel _ c _ h rest => by
    have ih := rest.peelable
    subst h
    exact ⟨c.2, ih⟩

/-- Peelable recording data gives a certificate. The recursion is on the list. -/
def Rec.ofPeelable : (is : List Nat) → (T : SSYTab) → Peelable Nested.unins T.rows is → Rec T
  | [], T, h => .nil T h
  | i :: is, T, h => .peel T ⟨i, h.1⟩ _ rfl (ofPeelable is _ h.2)

theorem Rec.toList_ofPeelable :
    ∀ (is : List Nat) (T : SSYTab) (h : Peelable Nested.unins T.rows is),
      (Rec.ofPeelable is T h).toList = is
  | [], _, _ => rfl
  | i :: is, _, h => by
    simp only [Rec.ofPeelable, Rec.toList, toList_ofPeelable is (uninsert _ ⟨i, h.1⟩).1 h.2]

theorem Rec.ofPeelable_toList : ∀ {T : SSYTab} (r : Rec T),
    Rec.ofPeelable r.toList T r.peelable = r
  | _, .nil _ _ => rfl
  | _, .peel T c T' h rest => by
    have ih := ofPeelable_toList rest
    subst h
    simp only [Rec.toList, Rec.ofPeelable]
    rw [ih]

/-- On a certificate, `unrskR` is `Nested.unrsk` on the recorded indices. -/
theorem unrskR_eq : ∀ {T : SSYTab} (r : Rec T), unrskR r = Nested.unrsk T.rows r.toList
  | _, .nil _ _ => rfl
  | _, .peel T c T' h rest => by
    have ih := unrskR_eq rest
    subst h
    simp only [unrskR, Rec.toList, Nested.unrsk, ih]
    rfl

/-- `rskR` computes `Nested.rsk`. -/
theorem rskR_eq : ∀ w, ((rskR w).1.rows, (rskR w).2.toList) = Nested.rsk w
  | [] => rfl
  | x :: w => by
    have ih := rskR_eq w
    simp only [rskR, growR, Rec.toList, insert, Nested.rsk]
    rw [← ih]

/-! ## What still computes -/

-- The underlying lists of an `RSKOut` value compute by `decide`: the proof fields are never
-- evaluated, only projected away.
example : (rskOut (n := 3) ⟨[3, 1, 2], rfl⟩).1 = ([[1, 3], [2]], [0, 1, 0]) := by decide
example : ((rskR [3, 1, 2]).1.rows, (rskR [3, 1, 2]).2.toList) = ([[1, 3], [2]], [0, 1, 0]) := by
  decide
example : unrskOut (rskOut (n := 3) ⟨[3, 1, 2], rfl⟩) = ⟨[3, 1, 2], rfl⟩ := by decide
example : unrskR (rskR [3, 1, 2]).2 = [3, 1, 2] := by decide

-- A concrete semistandard tableau and corner need a proof by hand: `SSYT` and `Corner` have no
-- `Decidable` instance, so `decide` does not apply.
example : SSYTab := ⟨[[1, 3], [2]], by simp [SSYT, Good, Sorted, ColStrictFull, Col2]⟩
example : Corner 0 [[1, 3], [2]] := by simp [Corner]

end RMT.RSK.Intrinsic
