# External resource: the Stacks Project in Lean (Axiom)

**What.** A Lean 4 formalization of [the Stacks Project](https://stacks.math.columbia.edu/), built on
Mathlib and indexed by Stacks tag. Each formalized tag carries `@[stacks TAG]`, and EGA/SGA items carry
`@[ega …]` / `@[sga …]`.
- Website: <https://stacks.axiommath.ai/>, which links each tag to its Lean code.
- Source: <https://github.com/AxiomMath/Stacks>.
- License: Apache-2.0. The Stacks Project text itself is under the GFDL.

**Pinned for reference** (not a dependency):

| | Stacks | RMTlib (for comparison) |
|---|---|---|
| commit | `f56a316ddf7a930906d88b78d6f9a2668cffd0cf` (`main`, "chore: seal sheafification def…") | see `lake-manifest.json` |
| toolchain | `leanprover/lean4:v4.35.0` | `v4.37.0-rc1` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`) | `31ce06e…` |
| size | 64,216 `.lean` files (about 64,000 modules; 44,630 files under `AlgebraicGeometry`) | about 9,000 jobs |
| tiers | `StacksCore` (human-reviewed), `StacksFrontier` (AI-written, kernel-checked, not yet reviewed) | — |
| axioms | `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide` (README) | the same |

**Why it is not a Lake dependency.**
- The toolchain and Mathlib differ from RMTlib's: 4.35.0 / `56a0058`, against RMTlib's 4.37.0-rc1 / `31ce06e`.
- A full build compiles about 64,000 modules, and Axiom's cache for compiled Stacks modules is announced but not yet available.

So RMTlib cites Stacks declarations and does not import them. A statement RMTlib needs is restated, citing the tag, the Stacks declaration and the commit above, the way RH-Dual's frozen bridge restates `plRule`.

**How to consult it.**
- **By tag:** the website, or `#stacks_tags` / `#stacks_tags!` after `import Stacks` in a Stacks checkout.
- **By file**, from a local sparse, blobless clone that RMTlib keeps outside the repository at
  `~/work/external/AxiomStacks`. It is 13 MB of history plus whatever is checked out. To recreate it:
  ```
  git clone --depth 1 --filter=blob:none --sparse https://github.com/AxiomMath/Stacks AxiomStacks
  cd AxiomStacks
  git ls-tree -r --name-only HEAD | grep <topic>               # find modules without downloading them
  git sparse-checkout add StacksFrontier/AlgebraicGeometry/GrassmannianScheme   # fetch only what you read
  ```
- **With MeaningLib's tools** (`index`, `grep`, `paths`, `join`): only once compiled `.olean`s exist, i.e. once Axiom's cache is published, or after a full local build on 4.35.0.

**Modules relevant to RMTlib's programme** (found by name in the tree, not yet read):

| RMTlib topic | Stacks modules (`StacksFrontier/AlgebraicGeometry/…` unless stated) |
|---|---|
| `Gr(k, n)`, Schubert cells (inventory row 6; #142, #151) | `GrassmannianScheme/`, `GrassmannianChart/` |
| flags (#141) | `FlagTower/` |
| `ℙⁿ`, `Proj`, closed subschemes (#129, #136) | `ClosedSubschemeProjectiveSpace/`, `ClosedSubschemeProjQuotient/`, `HProjective/`, `HProjectiveProper/`, `AmpleProjectiveImmersion/` |
| curves (the `ℙ¹`s; places row 7 by analogy) | `Curves/`, `CurveDegreeInvariance/`, `CurveIntersectionNumber/`, `CurveEulerBridge/`, `EllipticCurve/` |
| symmetric powers (`Symⁿ ℙ¹ = ℙⁿ`, #136) | `AffineSymmetricAlgebra/`, `AffineSymmetricPowerCompare/` |
| cyclotomics (#145, Bertrand) | `StacksCore/NumberTheory/Cyclotomic/{Basic,Gal}.lean` |

**Next use.** When a target of #136, #141, #142 or #154 needs an algebro-geometric statement, look it up here first and restate it with its tag.
