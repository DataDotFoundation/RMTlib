# Jacobi–Trudi in RMTlib: a direction

Status: plan, not yet started. Written before RMTlib and the RH formalisation
(`pdehaye/riemann-hypothesis-lean`) are recombined for further work.

## Why Jacobi–Trudi

Jacobi–Trudi (JT), `s_{λ/μ} = det (h_{λ_i − μ_j − i + j})`, works as a litmus test for proof
technique. It has many classical proofs: the `E(t)H(−t) = 1` matrix factorisation, the
bialternant, LGV lattice paths, Pieri induction, Cauchy–Binet over branching, and Fock/vertex
operators. As far as we know, Mathlib (at the pinned commit) has `hsymm`/`esymm` but no Schur
polynomials; **this is still to be checked (M0)**. So every project has to choose a route, and the
route it chooses tells you something.

Dehaye, *On an identity due to ((Bump and Diaconis) and (Tracy and Widom))*, Canad. Math. Bull.
54 (2011), arXiv:math/0601348, puts JT one level up:

* `Δ = exp (Σ_k k ∂_{p_k} ∂_{p̃_k})` (on `Λ(X) ⊗ Λ(Y)`: `exp (Σ_k p_k^⊥ p̃_k^⊥ / k)`), an operator
  "very similar to vertex operators".
* `Δ(BD^{λ∅} · BD^{∅μ}) = BD^{λμ}` and `Δ(TW^{λ∅} · TW^{∅μ}) = TW^{λμ}` (Thms 2–3), where
  `BD^{λ∅} = TW^{λ∅} = s_λ` is JT.
* Mechanism, from a summary of §5 (to be checked against the paper): `Δ = (Σ_ν s_ν s̃_ν)^⊥`
  (Cauchy kernel), so `Δ(s_λ s̃_μ) = Σ_ν s_{λ/ν} s̃_{μ/ν}`, and Cauchy–Binet gives the
  Tracy–Widom `d×∞ · ∞×d` determinant.

So the Bump–Diaconis / Tracy–Widom Toeplitz-minor identity is *JT differentiated by `Δ`*. To be
able to state this, a library needs JT as an **identity that can be skewed, contracted and acted
on**, not as a definition.

## What exists

### RMTlib

| Name | Content |
|---|---|
| `RMT.jacobiTrudi_one_variable` | skew JT in one variable is the interlacing indicator (a 0/1 staircase determinant) |
| `RMT.jacobiTrudiOne_eq_gtCount` | `det h_{ν_i−i+j}(1^n) = #GT(ν)`, via a Vandermonde factor and Weyl's dimension formula |
| `RMTlib/Tableaux/Pieri.lean` | imports JT; Lagrange identities, Weyl dimension (Vandermonde form) |
| `RMT.Fock.fischer`, `RMTlib/Fock/ClassFunction.lean` | Fischer pairing; on class functions it is the content-twisted Hall pairing (proved for `p₁^m`; general case only numerical). The docstring already names `Δ` |
| `bridge/RMTlibBridge/Interlacing.lean` | `cayley_interlacing_iff`: the RH formalisation's GGP interlacing condition |

### RH formalisation: four separate JT developments, no shared code

| # | Namespace / location | Ring | Schur defined as | Proved | Technique | Consumers |
|---|---|---|---|---|---|---|
| 1 | `GroundTheory.Heights₂.Heights.RestTerms` (`GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean`, `Statements.lean:56`) | ℚ, polynomial | `det completeSymmetric (λ_i − i + j)` | bialternant `det_pow_add_staircase` | `E(t)H(−t)=1` factorisation (`omitProduct`) | Schur at roots of unity (`SchSchurAtRootsOfUnity`), `OtherFactorFormula` (fibre degree via `numStandardTable`), and `UpperTheory.Gal.Schur` (`Comparison₂`, `SchurY*`, Hecke/Lefschetz traces) |
| 2 | `GlobalTheory.JSW` (`Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`) | ℤ, polynomial | `schur = jtDet hsymm` (`rfl`) | padding, `jacobi_trudi_alternant_expansion`, `bialt_int`, Pieri `esymm_mul_schurPolynomialJacobiTrudi` | antisymmetrisation and sorting; block-triangular padding | Cauchy identity (`cauchy_formal`), giving local Rankin–Selberg factors (`cauchy_locL`); Shintani formula (Whittaker = Schur in Satake parameters) |
| 3 | `PositivityTheory.RgJS` (`Development/WeilBound/…/JacquetShalikaBounds/CauchyIdentity/`) | ℂ, numerical | `jt α l = det hZ (l_j − j + i)` (**transposed** indexing) | Prop chain `HGen → ERel → AltJT → SchurJT`, `JTPad` | same factorisation as #1, redone over ℂ | analytic Cauchy (`cauchy_variation_inequality`, then `CauchyAll`), Jacquet–Shalika rigidity, GL₃×GL₂, `SchurInverseEqReversedNeg` |
| 4 | `RemainderTerms/IsFlagIntegralOne.lean` | ℚ | `schurPoly` via `hAt` | nothing (definition only) | — | flag integrals, `frobChar` |

The four developments are imported along the main chain. **Whether the final proof term uses them
has not been checked**: that needs a full build and a constant-dependency audit.

What they have in common: Schur is defined as the JT determinant, and the bialternant is proved
from it. None of them has skew Schur functions, `p^⊥`, LGV, tableaux, or Cauchy–Binet over
branching. The Cauchy identity, which is the kernel of `Δ`, is proved twice (#2, #3), but only as
a summation formula for L-factors, never as an operator.

## Design principles for RMTlib

1. **Schur is not defined as a JT determinant.** Define `s_{λ/μ}` combinatorially (weighted
   Gelfand–Tsetlin patterns, extending `gtCount`, or SSYT), so that JT is a theorem.
2. **Skew first.** State everything for `λ/μ`; the straight shape is `μ = 0`.
3. **One JT matrix, generic coefficients.** `jtMat (h : ℤ → A) (λ μ : Fin n → ℕ) i j :=
   h (λ_i − μ_j − i + j)` over any `CommRing A`, with `h k = 0` for `k < 0` and `h 0 = 1`. Prove the
   transposition, padding (`JTPad`) and ring-hom lemmas once. Convert the RH conventions (#1–#3)
   in the bridge, not in RMTlib.
4. Follow the repo conventions: unproved targets are `Prop`s (no `sorry` in the library), computations
   use `decide`/`#guard`, every public declaration has a docstring.

## Milestones

**M0. Survey.** Check what Mathlib at the pinned commit has: `hsymm`, `esymm`, `psum`, Newton
identities, `Matrix.det_mul`, Cauchy–Binet (`Matrix.det_mul` for non-square matrices?), and any
Schur or Young-tableau API.

**M1. Definitions.** `jtMat` as above. Skew Schur `s_{λ/μ}(x_1..x_n)` as a sum over GT patterns
(interlacing chains `μ ≺ ν¹ ≺ … ≺ λ`, already present as `GTStep`/`Interlaced`), weighted by
`∏ x_k^{|ν^k|−|ν^{k−1}|}`. `#guard` checks against `gtCount` at `x = 1`.

**M2. Skew JT by branching.** This is the route RMTlib is set up for, and it differs from all
four RH developments:
* `h_k(X ∪ Y) = Σ h_i(X) h_{k−i}(Y)`, so infinite upper-triangular Toeplitz matrices multiply:
  `T(H_{X∪Y}) = T(H_X) · T(H_Y)`.
* One variable: `jacobiTrudi_one_variable` (done).
* Cauchy–Binet on the minors `(λ, μ)` of a product gives
  `det jtMat_{X∪Y}(λ, μ) = Σ_ν det jtMat_X(λ, ν) · det jtMat_Y(ν, μ)`, which is the branching
  rule for `s_{λ/μ}`. Induct on the number of variables.
* Finite truncation: only rows and columns below `λ_1 + n` matter. This is the main
  formalisation cost.

**M3. Corollaries and comparisons.** Bialternant `a_{λ+δ} = s_λ a_δ`; Pieri (`e_j`, `h_j`); dual
JT (`e`) via `ω`; `s_ν(1^n)` recovers `jacobiTrudiOne_eq_gtCount`. In `bridge/`: one theorem per
RH development (#1–#4) saying its object equals RMTlib's `s_λ` under the conversion of conventions.
That shows the RH formalisation's four JT developments factor through one.

**M4. The operator layer (Dehaye 2006/2011).**
* Setting: `ℚ[p_1, p_2, …] ⊗ ℚ[p̃_1, p̃_2, …]`, truncated by degree (`MvPolynomial (ℕ ⊕ ℕ) ℚ`
  with homogeneous components). On each graded piece `Δ` is a finite sum, so no analysis is needed.
* `pPerp k := k • ∂/∂p_k`; `Δ := exp (Σ_k pPerp k ∘ pPerpTilde k / k)`, the exponential being
  locally nilpotent.
* Design decision: in `p`-coordinates, `s_λ` must be expressed through `h` (Newton), and that is
  JT again. Keep the GT definition of M1 as the *primary* one, and prove its image in `Λ` (stable in
  `n`) agrees.
* Targets, as `Prop`s first:
  1. `Δ = (Σ_ν s_ν s̃_ν)^⊥` (Cauchy kernel adjoint under the Hall pairing).
  2. `Δ (s_λ · s̃_μ) = Σ_ν s_{λ/ν} s̃_{μ/ν}`.
  3. Cauchy–Binet then gives the Tracy–Widom determinant; this is Theorem 3 of the paper.
  4. Bump–Diaconis side (Theorem 2): needs characters `χ^λ` and Laguerre polynomials (Lemma 5).
     Defer.

**M5. Toeplitz minors.** `σ(t) = exp(Σ p_k t^k/k + p̃_k t^{−k}/k) = Σ d_k t^k`, minors
`det (d_{λ_i − μ_j − i + j})`. An algebraic (formal, degree-truncated) statement of
`R^{λμ} = TW^{λμ}`, using the Wiener–Hopf factorisation `σ = σ⁺σ⁻`. The Heine/Gessel integral over
`U(n)` and the `n → ∞` limit are stretch goals.

**M6. Back to Fock.** Link `Δ` with `RMT.Fock.fischer`. `ClassFunction.lean` says the Fischer
pairing on class functions is the Hall pairing twisted by `∏ (N + c − i)`, and that `Δ` gives the
untwisted one. Target: the general Schur-basis statement, and the large-`N` limit. This is where
RMTlib meets the RH formalisation's `fockQ` and `hookNorm` (`bridge/RMTlibBridge/FockNorm.lean`).

## For the recombination

* RH consumers that an operator-level JT would serve directly: the Cauchy identity
  (`cauchy_formal`, `cauchy_variation_inequality`), Pieri in the Shintani formula, and evaluations at
  roots of unity (`SchSchurAtRootsOfUnity`, which is a border-strip/character statement).
* Before relying on any of these: audit which JT constants the proof terms of `riemannHypothesis`
  and the GRH statements actually depend on (full build plus constant closure; the import closure
  is the whole repo, all 175,187 files).
* Litmus rubric, one row per occurrence: route (factorisation, bialternant, LGV, Pieri, branching,
  operator); scalar ring; indexing convention; skew or not; definition vs theorem; reused or
  redone; on the main path or not.

## Loose ends

* Paper §5 (mechanism through the Cauchy kernel) and Eq. (5) (Tracy–Widom formula) were read only
  in summary. Check them against the text.
* The README says `HookLengthSquare` is proved only for `k < 3`; `main/RMTlibTargets/Statements.lean`
  points to `RMT.hookLengthSquare_holds`. Reconcile.
