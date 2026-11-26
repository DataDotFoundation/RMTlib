# Certificates against TauCetiRoadmap statements (not built by `lake build`)

Self-contained Lean files that port a roadmap's definitions verbatim and prove some of its targets. Each file
must compile **at the roadmap's own pins** (TauCetiRoadmap: Mathlib `1b1ccf4`, Lean `v4.36.0-rc2`) and at
RMTlib's. Check it with `lake env lean <file>`, run inside a project at those pins.

| file | roadmap | proves | checked at |
|---|---|---|---|
| `HookNumber.lean` | ShortGRH / IntegralRepresentationsOfGeneralLinearGroups §1.1 (a)(b)(g)(i), §2.2 (e) | the one-row case `H(κ) = ∏_τ κ_τ(1)!` (`hookNumber_one_row`) | roadmap pins (1b1ccf4 / v4.36.0-rc2) and RMTlib pins, 2026-11-26 |

Not proved here: the general value `H(κ) = ∏_τ (hook product of λ_κ(τ, ·))`. It is checked exactly on 29 weights
(RMTlib#177); the route is the first-column Cayley identity.
