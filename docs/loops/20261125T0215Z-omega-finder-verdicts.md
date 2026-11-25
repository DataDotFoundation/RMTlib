# Loop 2: the ω-twin finder (verdicts)

Verdicts on `20261125T0210Z-omega-finder-predictions.md`. Checks: `lake build --wfail` and `lake test` both exit 0. `RMTlibExamples/Omega.lean` pins the summary and the three acceptance rows. Tags: **computed** (a run in this loop), **inferred**.

| | Prediction | Verdict | Tag |
|---|---|---|---|
| OF1 | (0.8) the three acceptance rows | **held, after two fixes** | computed |
| OF2 | (0.6) at most 10 shape laws, the bulk operator | **held**: 5 laws and 1 `involutive`; 21 operator | computed |
| OF3 | (0.5) at least 2 laws without a name hit | **failed**: 0 | computed |
| OF4 | (0.75) exactly 2 recorded directly | **failed**: 3 | computed |
| OF5 | (0.6) at most 10 `unknown` | **failed**: 14 | computed |
| OF6 | (0.8) under 60 s | **held**: 8.8 s for all of `RMT` (1822 theorems) | computed |

## Details

**OF1.** The first run was wrong in two ways, and both were defects of the tool:
1. **No law showed as recorded.** Lean moves the proof fields of `omegaOcc` (and of `omegaContentProd`) into auxiliary `….proof_k` declarations, so the instance values never name the law directly. The finder now looks through these auxiliary declarations (`usedThroughAux`).
2. **`conjV_conjV` came out `unknown`.** `Expr.find?` visits partial applications: in `conjV N (conjV K lam)`, the subterm `@conjV K N` has the free variable `N` as its last argument and was taken as the shape. The finder now matches whole application spines only.

With these fixes:
- `contentProd_transpose` is `id`, recorded by `omegaContentProd`, with twin `f ↦ fun z ↦ f (-z)`;
- `occ_transpose` is `¬`, recorded by `omegaOcc`, with twin `z ↦ -1 - z`;
- `neg_one_pow_card_transpose` is `invariant`.

`casimirEig_transpose`, `archimedean_contentProd_transpose` and `hypGram_transpose` are in RH-Dual now. There, the same finder with RH-Dual's spec is the acceptance test.

**OF3.** Every law found has a name hit. RMTlib names its ω laws consistently, so the shape search found nothing that `grep` misses. This is a fact about RMTlib, not about the finder: in RH-Dual, and in Alpöge's proof, names follow other conventions.

**OF4.** `neg_one_pow_card_transpose` is also recorded, inside `omegaHookContent`'s proof. "Recorded" here means "used by the instance", which is broader than "is the instance's `map_transpose`".

**OF5.** The 14 `unknown` rows fall into three groups:
- **12 are real ω statements outside the `OmegaCovariant` shape:**
  - the `conjV` lemmas on padded shapes (`sum_conjV`, `lt_conjV_iff`, `conjV_le`, `antitone_conjV`, `gtStep_conjV_iff`, `sum_interl_conjV`), where `conjV` changes the length of the padded shape (`Fin N → Fin K`);
  - the dual Jacobi–Trudi (`schurV_conjV_eq_eDet`, `schurV_eq_eDet_conjV`) and dual Cauchy (`dual_cauchy`, `dual_cauchy_one`) identities;
  - `transpose_of` and `Statement.transpose`, where the correction of the V-coding is `i ↦ −vCoding (rev i)`, with a reversal of the index.
- **2 are name hits with no involution in the statement:** `transposeV`, `content_swap`.

## What the loop produced

1. **The finder**, `#involution_laws`.
   - It imports only `Lean`, so that it can move to MeaningLib as an "involution law" rule kind.
   - RMTlib's ω spec is `RMT.Frames.omegaSpec`.
2. **The to-do list.** Two laws are not recorded:
   - `conjV_eq_zero_iff`. `OmegaCovariant` cannot record it: its family is indexed by `YoungDiagram`, while `conjV` acts on padded shapes of varying length.
   - `MultisetHook.Stable.transpose`, which has the shape `preserved`. An `OmegaCovariant` instance needs the equivalence `Stable t μ′ ↔ Stable t μ`. That follows from `Stable.transpose` applied twice, using `transpose_transpose`.
3. **A requirement for `OmegaCovariant`** (inferred): a version for padded shapes, or a transport along `rowsOf`. This would record the `conjV` laws and the dual Cauchy and Jacobi–Trudi identities. It is the "padded shapes" case already flagged in `docs/omega-twin-finder.md`.

## Next loop, proposed

- Record `Stable.transpose` as an `OmegaCovariant` instance (`out = id` on `Prop`), so that the to-do list drops to the padded-shape gap.
- Propose the generic part upstream (MeaningLib): rule kind "involution law", whose rows become MeaningLib#5 item 1 judgements.
- Run the finder with RH-Dual's spec on `RHDual.Places` (RH-Dual's ω twin ledger), which is what RMTlib#4 asks.
