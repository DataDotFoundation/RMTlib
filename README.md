# RMTlib

A Lean 4 library of results in random matrix theory, in an extended sense: the combinatorics
that random matrix computations reduce to. Everything is proved; there is no `sorry` and no
`axiom`, and the main theorems use only `propext`, `Classical.choice` and `Quot.sound`
(`RMTlibExamples/AxiomAudit.lean`).

| Area | Modules |
|---|---|
| RSK and growth diagrams (including dual and super RSK) | `RMTlib.RSK`, `RMTlib.Growth` |
| Young tableaux: hook length, hook content, multiset hooks, interlacing | `RMTlib.Tableaux` |
| Symmetric functions: Cauchy identities, Jacobi–Trudi, content products, `ω`-covariance | `RMTlib.Symmetric` |
| Fock space: Fischer pairing, power sums, Casimir, Virasoro | `RMTlib.Fock` |
| Fermions: Maya diagrams, charge | `RMTlib.Fermion` |
| The Keating–Snaith constant | `RMTlib.KeatingSnaith` |

`ω` (transposition `λ ↦ λ′`, `h ↔ e`, `N ↦ −N`) is tracked as data:
`RMT.Symmetric.OmegaCovariant` records how a statistic of a shape changes under transposition
(`RMTlib/Symmetric/OmegaCovariant.lean`). A finder for `ω` laws by statement shape is specified
in `docs/omega-twin-finder.md`.

## Build

Lean `v4.33.1` (`lean-toolchain`), Mathlib pinned in `lakefile.toml`.

```bash
lake exe cache get    # prebuilt Mathlib
lake build --wfail    # warnings are errors
lake test             # examples and the axiom audit
```

`scripts/` holds exact checks (stdlib Python, run as `python3 -I scripts/<name>.py`) that
accompany some modules; `docs/` holds design notes.

## Origin

Split on 2026-11-24 from the `combinatorics/` folder of `DataDotFoundation/RMTandMeaningLib`
(commit `966e85f` and its predecessors), which uses this library as a dependency. Module names are
unchanged.
