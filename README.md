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
| Moments: Dehaye's combinatorial form of the CFKRS recipe for `U(N)` (Theorem 3), proved for `M ≤ 1`, checked exactly beyond | `RMTlib.Moments` |

`ω` (transposition `λ ↦ λ′`, `h ↔ e`, `N ↦ −N`) is tracked as data:
`RMT.Symmetric.OmegaCovariant` records how a statistic of a shape changes under transposition
(`RMTlib/Symmetric/OmegaCovariant.lean`). A finder for `ω` laws by statement shape is specified
in `docs/omega-twin-finder.md`.

## Direction: moments seen through frames, tested by gaps

`RMTlib.Moments` is meant to read itself through a frame of understanding: in the places frame, the
`U(N)` moment computation is the archimedean side (rank `N`) of a local identity whose finite-place
side has parameter `T = p^{−s}`. It is meant to be tested by its consequences for gaps between
zeros (Hall's method turns moment coefficients into gap bounds). The frame tools come from
[MeaningLib](https://github.com/DataDotFoundation/MeaningLib); both parts are planned, not built.

## Build

Lean `v4.35.0` (`lean-toolchain`), Mathlib pinned in `lakefile.toml`.

```bash
lake exe cache get    # prebuilt Mathlib
lake build --wfail    # warnings are errors
lake test             # examples and the axiom audit
```

`scripts/` holds exact checks (stdlib Python, run as `python3 -I scripts/<name>.py`) that
accompany some modules; `docs/` holds design notes. `scripts/check_pins.py` checks the Lake pins
(canonical copy in MeaningLib; keep it byte-identical, `check_pins.py bump MeaningLib` refreshes it).

## Origin

Split on 2026-11-24 from the `combinatorics/` folder of `DataDotFoundation/RMTandMeaningLib`
(commit `966e85f` and its predecessors), which uses this library as a dependency. Module names are
unchanged.
