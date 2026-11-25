# Loop 2: the ω-twin finder (predictions)

Written before any code of this loop. The verdicts go in a later file in this folder. Issue: RMTlib#4 (from RH-Dual); specification: `docs/omega-twin-finder.md`.

**Loop.**
- **Target:** every theorem under `RMT`.
- **Tool:** a new command, `#involution_laws spec in N`, which needs only `import Lean`, so that it can move to MeaningLib. Its spec gives:
  - the involutions: `YoungDiagram.transpose`, and the padded `RMT.Symmetric.conjV`;
  - the operator involutions: `RMT.Fock.Virasoro.omega`, `RMT.Fock.DehayeDelta.omega2` and `RMT.Fock.DehayeDelta.omegaL`;
  - the other involutions: `Matrix.transpose`;
  - the recording structure: `RMT.Symmetric.OmegaCovariant`.
- **Shapes:**
  - `id`: `F a μ′ = F b μ`;
  - `¬`: `P μ′ a ↔ ¬ P μ b`;
  - `out g`: `F a μ′ = g (F b μ)`, where `g` does not mention `μ`;
  - `out(μ)`: as `out g`, but `g` mentions `μ`, e.g. `c μ * ·`;
  - `invariant`: both sides are the same family with the same arguments;
  - `preserved`: `P μ → P μ′`;
  - `operator`;
  - `other involution`;
  - `unknown`.
- **Metric:** the number of ω laws found that no `OmegaCovariant` instance records (the to-do list).

**Adapted acceptance test.** `casimirEig_transpose`, `archimedean_contentProd_transpose` and `hypGram_transpose` from the spec are not in RMTlib: they are in RH-Dual now, and there is no `Matrix.transpose` law in RMTlib. In RMTlib:
- `contentProd_transpose` must come out as `id`, with instance `omegaContentProd`;
- `occ_transpose` must come out as `¬`, with instance `omegaOcc`;
- `neg_one_pow_card_transpose` must come out as `invariant`.

**Baseline (computed, `grep` of theorem names at `52bdf97`).** 40 theorem names in `RMTlib/` contain `transpose`, `conj`, `omega` or `swap`. 21 of them are `omega*` operator lemmas in `Fock`, 11 are `conjV` lemmas, 2 are lemmas about `OmegaCovariant` itself, and the rest are about Maya diagrams or contents.

**Predictions:**
- **OF1** (p = 0.8): the three acceptance rows come out as stated above.
- **OF2** (p = 0.6): at most 10 theorems are classified as shape laws (`id`, `¬`, `out g`, `out(μ)`, `invariant`, `preserved`). The bulk of the hits are operator laws.
- **OF3** (p = 0.5): at least 2 shape laws have no name hit, i.e. their names mention none of `transpose`, `conj`, `omega` or `swap`.
- **OF4** (p = 0.75): exactly 2 laws are recorded by an instance that names them directly (`contentProd_transpose`, `occ_transpose`). Every other shape law is on the to-do list.
- **OF5** (p = 0.6): at most 10 rows are `unknown`.
- **OF6** (p = 0.8): the whole scan of `RMT` runs in under 60 s.
