import RMTlib

/-!
# The ω-twin finder on RMTlib (`#involution_laws`)

Loop 2 (`docs/loops/`), RMTlib#4. The finder classifies every theorem under `RMT` that mentions
`ω` (`YoungDiagram.transpose`, `conjV`) or its operator form, by statement shape, and names the
`OmegaCovariant` instance that records each law. The laws with no instance are the to-do list.
The counts are pinned here; the full table is `#involution_laws RMT.Frames.omegaSpec in RMT`.
-/

/--
info: involution ω, spec RMT.Frames.omegaSpec, on RMT: 58 rows, 9 laws, 6 not recorded
  id: 2
  ¬: 2
  out g: 2
  out(μ): 1
  invariant: 1
  preserved: 1
  involutive: 2
  operator: 21
  other involution: 5
  unknown: 21
name hits: 52; laws with a name hit: 9; laws without one: 0
-/
#guard_msgs (whitespace := lax) in
#involution_laws RMT.Frames.omegaSpec in RMT summary

-- The three acceptance rows of `docs/omega-twin-finder.md`, as they stand in RMTlib.
/--
info: involution ω, spec RMT.Frames.omegaSpec, on RMT.Symmetric.contentProd_transpose: 1 rows, 1 laws, 0 not recorded
  id: 1
name hits: 1; laws with a name hit: 1; laws without one: 0
RMT.Symmetric.contentProd_transpose (RMTlib.Symmetric.WeightedCauchy): id  [recorded: [RMT.Symmetric.omegaContentProd]]
    twin: f ↦ fun z ↦ f (-z)
    out: id
-/
#guard_msgs (whitespace := lax) in
#involution_laws RMT.Frames.omegaSpec in RMT.Symmetric.contentProd_transpose

/--
info: involution ω, spec RMT.Frames.omegaSpec, on RMT.MultisetHook.occ_transpose: 1 rows, 1 laws, 0 not recorded
  ¬: 1
name hits: 1; laws with a name hit: 1; laws without one: 0
RMT.MultisetHook.occ_transpose (RMTlib.Tableaux.MultisetHook.Maya): ¬  [recorded: [RMT.Symmetric.omegaOcc]]
    twin: z ↦ -1 - z
    out: Not
-/
#guard_msgs (whitespace := lax) in
#involution_laws RMT.Frames.omegaSpec in RMT.MultisetHook.occ_transpose

/--
info: involution ω, spec RMT.Frames.omegaSpec, on RMT.Symmetric.neg_one_pow_card_transpose: 1 rows, 1 laws, 0 not recorded
  invariant: 1
name hits: 1; laws with a name hit: 1; laws without one: 0
RMT.Symmetric.neg_one_pow_card_transpose (RMTlib.Symmetric.OmegaCovariantInstances): invariant  [recorded: [RMT.Symmetric.omegaHookContent]]
    twin: none
    out: id
-/
#guard_msgs (whitespace := lax) in
#involution_laws RMT.Frames.omegaSpec in RMT.Symmetric.neg_one_pow_card_transpose
