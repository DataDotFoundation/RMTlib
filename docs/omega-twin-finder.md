# To do: a finder for `ω` laws by statement shape

**Question.** Which theorems of the library are `ω` laws (`F p μ′ = out μ (F (twin p) μ)`), whether
or not anyone has recorded them as an `OmegaCovariant` instance?

**Status:** not started. This note is the specification. The structure it feeds is
`RMT.Symmetric.OmegaCovariant` (`RMTlib/Symmetric/OmegaCovariant.lean`), with four
instances in `OmegaCovariantInstances.lean`.

## Why statement shape, not a tag

The tag `@[conj_symmetric]` (`tools/RMTlib/Places/ConjSymmetric.lean`) finds only what someone marked,
and it marks one definition (`contentProd`). A search of names alone (computed, `grep`, at
`2b1ebca`) finds 5 theorems named `*_transpose` and about 64 theorems with `transpose`, `conj`,
`omega` or `swap` in their names, most of them unmarked. A finder that reads the elaborated
statements sees all of them, whatever they are called, and also catches false friends.

## What to match

Read each module's `.olean` with `readModuleData`, without importing it, as the frame engine's
witness checker does (`tools/scripts/grh_frame_leancheck.lean`). For each theorem, after
`∀`-telescoping, classify the conclusion:

| shape | example | candidate `twin` / `out` |
|---|---|---|
| `F a (μ.transpose) = F b μ` | `contentProd_transpose` | `a ↦ b`, `out = id` |
| `F a μ.transpose = g (F b μ)` with `g` a head symbol not mentioning `μ` | `casimirEig_transpose` (`g = Neg.neg`) | `a ↦ b`, `out = g` |
| `F a μ.transpose = c μ * F b μ` | `archimedean_contentProd_transpose` (`c = (−1)^{|μ|}`) | `a ↦ b`, `out μ = (c μ * ·)` |
| `P μ.transpose a ↔ ¬ P μ b` | `occ_transpose` | `a ↦ b`, `out = Not` |
| other occurrences of `YoungDiagram.transpose` (or `ω` on `Sym`/`Λ`: `h ↔ e`) | — | listed as `unknown`, with the term |

`μ` must be a bound variable of type `YoungDiagram` (or the padded shapes `Part`, through
`contentProdP_rowsOf`). Matrix transposition (`Matrix.transpose`, as in `hypGram_transpose`,
`scholze/RMTlib/Places/NullDatum.lean:94`) is a different involution: report it as `other involution`,
never as an `ω` law.

`ω` also appears at the level of operators, not shapes: `RMT.Fock.Virasoro.omega_L1`,
`omega_L0`, …, `RMT.Places.Hardy.omegaDual_*`, `RMT.Fock.WeilCauchy.omegaL_CK`,
`RMT.Fock.DehayeDelta.omega2_delta` (seen in the axiom audit, `main/RMTlibExamples/Axioms.lean`).
These are laws of the form `ω ∘ A = A' ∘ ω` for an involution `ω` of Fock space or of `Sym`. They
are a second shape for the finder (`operator law`), and a second structure to write later (`ω` as an
involutive algebra map with a twin on operators). Keep them in a separate column; do not merge
them with the shape laws.

## Output

Following the repository's rule for tools (rule-based witness statements or `unknown`, no reader
verdicts), one row per theorem:

`decl  module  shape  twin-witness  out-witness  instance?`

where `instance?` names the `OmegaCovariant` instance that already records the law, or is empty. The
empty rows are the to-do list. For each one, the finder can also emit the Lean skeleton of the
instance (`twin`, `out`, `map_transpose := <decl>`), leaving the two involution fields to be proved.

## Acceptance test

On the commit that introduces it, the finder must:

1. classify `contentProd_transpose`, `occ_transpose`, `casimirEig_transpose` and
   `archimedean_contentProd_transpose` in the first four rows, with the twins recorded in
   `OmegaCovariantInstances.lean`;
2. report `hypGram_transpose` as `other involution`;
3. state how many of the 64 name hits are `ω` laws, and how many `ω` laws have no name hit.
   Predictions for (3) are logged before it is run.

## Lane

Lane B (Lean metaprogram over `.olean` files, plus a stdlib Python driver). It needs no proof build
and belongs in RMTlib, not in the programme repository.
