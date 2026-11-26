# RMTlib.RSK — three proofs, three recursion schemes

A Lean 4 formalization showing that the Robinson–Schensted–Knuth correspondence is
invertible, proved three times. Each version uses a different recursion scheme, and each
proof is a recursion of the same kind as the function it is about. There are no
dependencies (no Mathlib).

Eight further modules (see [The landscape](#the-landscape-one-algorithm-many-recursion-schemes))
vary the recursion scheme one thing at a time: folds, fuel, rows instead of a grid, inductive
relations, mutual recursion, generated induction principles, invariants in the types, and a
sum measure (jeu de taquin). Each says in its docstring what the scheme cost and bought.

```bash
lake build RMTlib.RSK.Growth RMTlib.RSK.Semistandard RMTlib.RSK.Intrinsic  # this part only
lake build RMTlibExamples.RSK                         # runs and cross-checks (also run by `lake test`)
```

Ported from `RSK/` in [`pdehaye/MMT`](https://github.com/pdehaye/MMT) (up to commit
`63551a5`); namespace `RMT.RSK`. It builds with RMTlib's toolchain (Lean 4.35.0). The build contains no `sorry`,
and the main theorems use only Lean's standard axioms (`propext`, `Quot.sound`, and in
some cases `Classical.choice`). See `main/RMTlibExamples/Axioms.lean`.

## The three versions

| Module | Algorithm | Recursion scheme | Measure |
|---|---|---|---|
| `RMTlib.RSK.Nested` | Row bumping | Structural recursion, nested two levels deep (along a row inside down the rows) | none needed |
| `RMTlib.RSK.Zipper` | Row bumping | One tail recursion over a zipper each way, well-founded | `(below.length, row.length)` down, `(above.length, rev.length)` up |
| `RMTlib.RSK.Growth` | Fomin growth diagrams | One recursion over a grid each way, three calls per step, well-founded | `(i, j)` forward, `(n - i, n - j)` backward |

`RMT.RSK.Semistandard` adds, for both bumping versions, that uninsertion preserves
semistandardness, and shows the two bumping versions compute the same functions.

### `RMT.RSK.Nested`: nested structural recursion

The textbook presentation. Row insertion `rowIns` recurses along a row, and tableau
insertion `ins` recurses down the rows and calls `rowIns` at each one. Lean accepts every
definition as structural recursion. Each proof is an ordinary induction: a level-1 lemma
about one row (`rowUnins_rowIns`, `rowIns_rowUnins`) is used at each step of a level-2
induction about the tableau (`unins_ins`, `ins_unins`).

### `RMT.RSK.Zipper`: lexicographic well-founded tail recursion

The two levels are fused into one function per direction. `go` carries a cursor into the
tableau (rows above, the current row split at the cursor, rows below). Moving right
shortens the row, and a bump shortens `below` but starts a fresh row, so neither argument
decreases on every call: termination needs the lexicographic order on pairs. The inverse
`up` is the same machine run upwards, and each of its steps undoes a step of `go`.

Because `go` and `up` are loops, the proofs (`unins_go`, `ins_up`) are loop invariants. They
are stated for every intermediate state, which means generalising the accumulators, and
relate that state to the final answer of the other loop. Each is again one recursion on
the same measure.

### `RMT.RSK.Growth`: recursion over a grid

A permutation becomes a 0/1 grid and each grid point gets a shape:
`λ(i+1, j+1) = fwd λ(i,j) λ(i+1,j) λ(i,j+1) (σ i j)`. This recursion branches (three calls),
like a dynamic-programming recurrence, and is well-founded for the lexicographic order on
`(i, j)`. The top and right edges give P and Q, and `back` runs the grid backwards from
them.

Here all of the invertibility sits in one square: `bwd_fwd` says the backward local rule
undoes Fomin's forward rule. The global proof (`square_ok`, then `back_grow`) is one recursion
over the grid that checks every square meets the hypotheses of `bwd_fwd` and applies it.

## The landscape: one algorithm, many recursion schemes

The three versions above change more than one thing at a time (`Growth` changes the algorithm
as well as the recursion). The modules below each change one thing.

| Module | What changes | Termination | `decide` | Invertibility |
|---|---|---|---|---|
| `Nested` | (baseline) nested structural recursion | none needed | yes | native, layered induction |
| `Zipper` | one loop per direction, lexicographic WF | `decreasing_by` | no (`#guard`) | native, loop invariants |
| `Growth` | grid recurrence, lexicographic WF | `decreasing_by` | no, and exponential | native, one square (`bwd_fwd`) |
| `Fold` | the word level as `List.foldr`/`foldl`/`List.rec` | none needed | yes (if the step reduces) | one generic theorem for every step |
| `Fuel` | the zipper loop, structural on a fuel counter; also `partial def` | moved into a theorem | yes | transferred |
| `GrowthRows` | the growth grid, structural one row at a time | none needed | yes, polynomial | transferred |
| `Relational` | insertion as an inductive predicate | none | – | injectivity by rule induction, no inverse function |
| `Mutual` | the two levels as a `mutual` pair | WF on one `Nat` weight (structural refused) | with `decide +kernel` | native, `mutual_induct` |
| `FunInd` | the proofs, not the definitions: `fun_induction` | none in proofs | – | the zipper and growth theorems re-proved |
| `Intrinsic` | invariants in the types (subtype; indexed family) | none needed | on projections | hypothesis-free bijection |
| `JeuDeTaquin` | a different algorithm: slides, WF on a sum measure | `decreasing_by` | no; fuel version yes | native, one slide |

### `RMT.RSK.Fold`: the word level is generic

`rsk` is `List.foldr` of one insertion step (and `List.foldl` for ordinary left-to-right RSK,
`rskl_eq`). `unfold_fold` proves once, for every step function and invariant, that the unfold
inverts the fold; `unrsk_rsk` for `Nested` and for `Zipper` are then one line each, and
`fold_unique` identifies the existing definitions with the fold by `rfl`. The version written with
the eliminator `List.rec` must be `noncomputable` (the code generator does not support recursors)
but the kernel still evaluates it. The fold is structural, but `decide` only works when the step
reduces: with `Zipper.ins` as the step it is stuck.

### `RMT.RSK.Fuel`: termination as a theorem

The zipper loop `goF`, recursing on an explicit fuel argument. The definition needs no termination
proof; `goF_eq` shows that fuel above a crude numeric cost (row length plus boxes and rows below)
gives `Zipper.go`. That theorem needs one `Nat` measure instead of a lexicographic pair, and no
tableau invariant. The kernel evaluates the fuel version. All further facts are transferred
(`ins_eq_nested`, `unrsk_rsk`): fuel for computation, transfer for proofs. A `partial def` of the
same loop runs, but it is an opaque constant: nothing about its values can be proved. Linking it
with `implemented_by` to the fuel version gives fast code with a proved specification, but Lean does
not check that the two agree.

### `RMT.RSK.GrowthRows`: the same growth diagram, structural

Holds the algorithm fixed and changes only the recursion. Row `i+1` of the grid is computed from
row `i` by a sweep (`nextRow`), generically in the local rule as in `GrowthGeneric`. Everything is
structural, polynomial ((n+1)² local-rule applications each way) and evaluated by the kernel:
`decide` inverts permutations of size 10, where the WF `unrskGrowth` does not finish on size 6
even compiled. The price is the correspondence theorems (`rows_eq`, `backRows_eq`): nested
inductions that are mostly index bookkeeping. Invertibility is transferred from
`GrowthGeneric.back_grow`, not re-proved: rows change how the grid is computed, not how its squares
are checked. (`RMT.Growth.row` in `RMTlib.Growth.RSK` is an earlier structural row-by-row version,
with unpadded shapes and no invertibility proof.)

### `RMT.RSK.Relational`: invertibility without an inverse

`RowIns`, `Ins`, `RSK` are inductive predicates whose rules are the bumping steps; `ins_iff`
matches them with `Nested`. Determinism (`ins_det`) and injectivity (`ins_inj`, `rsk_inj`) are
proved by rule induction alone, with no uninsertion function anywhere. Injectivity needs only
sorted nonempty rows (`Good`), not the column condition. What the relational style does not give:
a computable inverse, or the existence direction. `rsk_surj` (every semistandard tableau with a
peelable corner sequence comes from a word) takes its witness from `Nested.unins`.

### `RMT.RSK.Mutual`: two states of a machine

`scan` (walk along the row with `x` in hand) and `descend` (carry a bumped value down) as a
`mutual` block. Lean refuses it as structural recursion: `scan` recurses on a row and `descend` on
a list of rows, and `scan` passes the rows below unchanged. It is WF on a single `Nat` weight. With
that measure the kernel evaluates it (`decide +kernel`, or `decide` after `unseal`); with the
zipper's lexicographic measure it does not. `unins_ins` is a direct mutual induction through the
generated `scan.mutual_induct`, using only the row-level lemma. Uninsertion is not written as a
mutual pair (its step returns to the row above).

### `RMT.RSK.FunInd`: generated induction principles

Same definitions, different proofs: eight theorems of `Zipper`, `Semistandard`, `Growth`,
`GrowthGeneric` and `Nested` re-proved with `fun_induction`, with statements checked identical to
the originals. No proof states a measure or a `decreasing_by`; the cases arrive split, with the
`if`/`match` conditions as hypotheses. Proofs are 10–25% shorter. Costs: case names are only
numbered; WF compilation leaves `List.attach`/`unattach` residue in induction hypotheses; a
theorem about two calls can follow only one. `Growth.square_ok` cannot be done this way: it is
strong induction on the lexicographic order, which no generated principle matches. The module has
a table of line counts.

### `RMT.RSK.Intrinsic`: invariants in the types

`SSYTab` carries its semistandardness proof; uninsertion takes a corner (`Cor T`), so it cannot be
called on bad input. This needed a new lemma, `ins_corner`: insertion grows the tableau at a
corner. With it, `rsk_peelable` characterises the image of RSK, and `rskEquiv n` is a bijection,
with no hypotheses, between words of length `n` and pairs (semistandard tableau, sequence of
corners peeling it). A second encoding makes the recording data an indexed family `Rec T`, so
`unrskR` recurses on the certificate and never checks a corner (`rskEquivR`). Costs: proofs inside
definitions, equality of dependent pairs, a "motive is not type correct" that forced restructuring,
and a careful constructor shape so that no cast appears in data. `decide` works on the projected
lists, not on the proof-carrying structures.

### `RMT.RSK.JeuDeTaquin`: a sum measure

A forward slide moves a hole right or down until it reaches an outer corner; termination is on
`(n - i) + (n - j)`, which drops by exactly one whichever way the hole moves. So the measure also
bounds the number of steps, and a fuel version with that much fuel is the same function
(`fwdFuel_eq`). Fillings are functions `Nat → Nat → Option Nat`, so skew shapes need no offsets and
the conditions are 2D and local. `rev_fwd_corner`: the reverse slide undoes the forward slide.
`fwd_tableau`: the forward slide preserves the tableau conditions on an order-convex shape. The
recursion depends on a lookup succeeding, so `decreasing_by` needs the match hypotheses
explicitly. The same theorem is proved by hand-written recursion and by `fun_induction`; the second
was shorter. Only single slides: rectification and Schützenberger's theorem are not done.

### What the landscape shows

* **Kernel evaluation** follows the recursion, not the algorithm. Structural recursion evaluates
  (`Nested`, `Fold`, `Fuel`, `GrowthRows`). WF recursion on a lexicographic measure does not
  (`Zipper`, `Growth`). WF on a single `Nat` measure can, with `decide +kernel` (`Mutual`). Fuel
  recovers evaluation for any loop.
* **Termination can be moved** from the definition into a theorem (`Fuel`), where it needs a
  cruder measure and no invariants. A measure that drops by exactly one per step is also a fuel
  bound (`JeuDeTaquin`).
* **Changing the recursion without changing the algorithm** costs a correspondence theorem, and
  then the invertibility proof is transferred rather than re-done (`Fuel`, `GrowthRows`).
* **Where the content sits**: the word level is generic (`Fold`); the content is in one insertion
  step (bumping), one square (growth) or one slide (jeu de taquin).
* **Inverse functions** are needed for round trips, not for injectivity (`Relational`). Existence
  always needs a witness.
* **Hypotheses move into types** at the price of proof terms in definitions (`Intrinsic`); this
  also forced the one new mathematical lemma (`ins_corner`).
* **Generated induction principles** remove termination from proofs and fit any recursion that
  follows one function, but not strong induction (`FunInd`).

## Diagonal symmetry and the recursion scheme

Two symmetries "around the diagonal" matter for RSK:

* **Transposing the grid** (`i ↔ j`): in a growth diagram this swaps the permutation with its
  inverse and P with Q, so RSK(σ⁻¹) = (Q, P).
* **Conjugating shapes** (rows ↔ columns, `λ ↔ λ′`): this relates row insertion to column
  insertion, and bosons to fermions (`GrowthSuper`).

None of the RSK modules states either symmetry yet. Whether one is cheap or hard to prove depends
on where it gets lost, and there are three levels at which to ask.

### Three levels

1. **The function.** The symmetry always holds here. RSK(σ⁻¹) = (Q, P) is a fact about the
   bijection, whichever way it is computed; all versions in this library compute the same function.
2. **The algorithm on paper.** This decides whether the symmetry is visible or deep, and has
   nothing to do with Lean.
   * Growth diagrams make it visible: the picture is symmetric, and Fomin's local rule treats its
     two sides alike (`Growth.fwd ρ μ ν x` uses `μ` and `ν` symmetrically). The symmetry is
     nearly a tautology.
   * Bumping hides it: P is built by insertion and Q only records where boxes landed, so the two
     come from unrelated processes. The symmetry is Schützenberger's theorem.
3. **The Lean encoding.** A symmetric algorithm can still lose the symmetry in its formal version,
   in three places:
   * **The recursion.** `Growth.grow` recurses on the lexicographic order of `(i, j)`, and
     `GrowthRows` goes row by row. Neither treats `i` and `j` alike, so a proof about the transpose
     cannot follow the definition's recursion.
   * **The data.** `Part` (padded row lengths) and `Tab` (a list of rows) are row-first, so a
     transpose is a computation that needs lemmas. With fillings as functions of a cell,
     `Nat → Nat → Option Nat` (as in `JeuDeTaquin`), it is a swap of arguments.
   * **Definitional versus propositional equality.** Even the local rule is symmetric only up to a
     lemma: `pmax μ ν = pmax ν μ` is not `rfl`. The symmetry is never completely free in Lean, but
     it is cheap when it reduces to one local lemma.

### Where each scheme stands

| Scheme | Level 2 (algorithm) | Level 3 (Lean encoding) |
|---|---|---|
| Bumping: `Nested`, `Zipper`, `Fold`, `Fuel`, `Mutual`, `Relational`, `Intrinsic` | broken: P and Q come from unrelated processes | cannot be repaired by encoding; transfer it instead |
| Growth grid: `Growth`, `GrowthGeneric` | kept: symmetric local rule | lost: lexicographic recursion, row-based `Part` |
| Growth rows: `GrowthRows` | kept | lost further: columns have no counterpart in the recursion |
| Jeu de taquin: `JeuDeTaquin` | depends on the slide (ties are broken asymmetrically) | cell-indexed data keeps transposition a swap of arguments |

So bumping breaks the symmetry at level 2, and no Lean encoding fixes that; the cheapest route is
to prove it for growth diagrams and transfer it along `Fomin.rsk_eq`. Growth diagrams keep it at
level 2, and the current files lose it at level 3, which is avoidable. Level 3 is where the
choices are ours: if the algorithm on paper is symmetric, a recursion and a data representation
that keep it symmetric in Lean can almost always be found, at the price of an equality theorem
linking back to any faster or row-first version.

### Keeping it: a recipe

* **Symmetric measure.** Recurse on `i + j` (anti-diagonals), or structurally on anti-diagonals
  ("wavefronts"), not on the lexicographic order. The sum is invariant under `i ↔ j`, so a proof
  about the transpose follows the same recursion as the definition.
* **Symmetric data.** Index tableaux and grids by cells, so that transposing is swapping arguments.
* **One local lemma.** Prove the local rule symmetric once; the global symmetry is then an
  induction on the symmetric measure: one local fact plus bookkeeping, the same shape as the
  invertibility proofs.
* **Transfer.** Keep bumping, `GrowthRows` and fuel versions as fast or row-first versions, each
  linked to the symmetric core by one equality theorem, and move the symmetry across it.

Conjugation is harder than transposition. Fomin's rule for permutations is not literally
self-conjugate, and `GrowthSuper`'s fermion rule is not the conjugate of its boson rule. There the
symmetry has to be an explicit map between two local rules, with the local correspondence proved
once.

**Not done yet.** The first step would be the local symmetry `Growth.fwd ρ μ ν x = Growth.fwd ρ ν μ x`,
then `grow σᵀ i j = grow σ j i` by induction on `i + j`, and RSK(σ⁻¹) = (Q, P) for bumping through
`Fomin.rsk_eq`.

## Main results

* `RMT.RSK.Nested.unrsk_rsk`, `RMT.RSK.Zipper.unrsk_rsk`: `unrsk (rsk w) = w` for every word `w`.
* `RMT.RSK.Nested.rsk_unrsk_ssyt`, `RMT.RSK.Zipper.rsk_unrsk_ssyt`: `rsk (unrsk t is) = (t, is)` for
  every semistandard tableau `t` and every sequence of corners `is` (`Peelable`).
* `RMT.RSK.Nested.unins_ssyt`: uninsertion at a corner sends a semistandard tableau to a
  semistandard tableau. It is an induction following `unins` that also tracks how the top row
  changed: one entry was replaced by a larger one, or removed from the end.
* `RMT.RSK.Zipper.ins_eq`, `RMT.RSK.Zipper.unins_eq`: the zipper's insertion equals the nested one on
  every input, and the two uninsertions agree on semistandard tableaux at corners. `ins_eq`
  is one recursion on `go`'s measure.
* `RMT.RSK.Growth.bwd_fwd`: the local rule is invertible on every square that can occur.
* `RMT.RSK.Growth.back_grow`, `RMT.RSK.Growth.backEntry_grow`: for a partial permutation, the
  backward grid rebuilds the forward grid and every matrix entry from the two outer edges.
* `RMT.RSK.Growth.unrskGrowth_rskGrowth`: inverse RSK by growth diagram recovers every
  permutation of `{0, …, n-1}`.
* `RMT.RSK.Nested.rsk_ssyt` (`Insert`): the insertion tableau is semistandard.
* `RMT.RSK.Intrinsic.ins_corner`, `RMT.RSK.Intrinsic.rsk_peelable`: insertion grows the tableau at
  a corner, so the recording data of `rsk w` is a peelable corner sequence. With `rsk_ssyt` and
  `rsk_unrsk_ssyt` this characterises the image of RSK; `RMT.RSK.Intrinsic.rskEquiv` packages it as
  a hypothesis-free bijection.
* `RMT.RSK.Fold.unfold_fold`: the word-level round trip, once for every step function.
* `RMT.RSK.Relational.rsk_inj`: injectivity of RSK by rule induction, without an inverse.
* `RMT.RSK.GrowthRows.unrskRows_rskRows`: inverse RSK by structural growth rows.
* `RMT.RSK.JeuDeTaquin.rev_fwd_corner`, `RMT.RSK.JeuDeTaquin.fwd_tableau`: slides are invertible
  and preserve tableaux.

`lake test` also checks, by running them, that the bumping versions (nested, zipper, fold, fuel,
mutual) agree on all words of length at most 5 over four letters, that growth diagrams give the
same P and Q as bumping on all permutations of size at most 4 (grid) and 6 (rows), and prints the
axioms of the main theorems.

## Scope

* The image of `rsk` is characterised (`rsk_ssyt`, `rsk_peelable`, `rsk_unrsk_ssyt`, and
  `Intrinsic.rskEquiv`), in terms of the recording data as a sequence of corners.
* The bumping versions return the recording data as the row index of each new box, not as
  the tableau Q. `RMTlibExamples.RSK` builds Q from it for the comparison.
* The proved growth versions `Growth` and `GrowthRows` handle permutations (and partial
  permutations). `GrowthKnuth` and `GrowthSuper` give local rules for ℕ-fillings and super-RSK
  with local invertibility and injectivity (`eq_of_edges`). `Growth`'s `grow` and `back` take
  exponential time; `GrowthRows` computes the same grids in polynomial time.
* The words are inserted from right to left so that the recursion is on `x :: w`.
  Ordinary left-to-right RSK is `rsk` of the reversed word (`Fold.rskl_eq`).
* Jeu de taquin covers single slides; rectification and Schützenberger's theorem are not proved.
