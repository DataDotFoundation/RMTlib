# Giambelli's identity in RMTlib

File: [`RMTlib/Symmetric/Giambelli.lean`](../RMTlib/Symmetric/Giambelli.lean), namespace `RMT.Symmetric.Giambelli`.
All results are sorry-free and use only `propext`, `Classical.choice` and `Quot.sound` (`RMTlibExamples/AxiomAudit.lean`).

## Statement

For a partition `λ` with Durfee square of side `d` and Frobenius coordinates `(α | β)`, where
`α_i = λ_i − i − 1` and `β_j = λ′_j − j − 1`:

  `s_λ = det (s_{(α_i | β_j)})_{i, j < d}`.

It is proved for any pair of symbols `h, e : ℤ → R` with `H(X) E(−X) = 1`, and then specialised.
The proof right-multiplies the Jacobi–Trudi matrix by the unitriangular matrix `((−1)^{j+k} e_{k−j})`,
which turns the rows below the Durfee square into unit rows. Frobenius complementarity then leaves the
minor on the legs.

## Declarations

| declaration | content | commit (PR) |
|---|---|---|
| `det_unitRows` | expansion of a determinant along unit rows | ac695b1 (#180) |
| `det_submatrix_rev` | reversing columns: sign `(−1)^{n(n−1)/2}` | ac695b1 (#180) |
| `durfee`, `frobA`, `frobB`, `rowL`, `colL` | Durfee square, arms, legs | ac695b1 (#180) |
| `lt_durfee_iff`, `frobB_lt`, `frobB_lt_n`, `frobB_ne` | Frobenius complementarity | ac695b1 (#180) |
| `HEPair`, `jt`, `hookV` | `(h, e)` pairs, Jacobi–Trudi determinant, hook symbol | ac695b1 (#180) |
| `giambelli_jt`, `jt_hook`, `giambelli_jt'` | Giambelli for any `(h, e)` pair | ac695b1 (#180) |
| `hePair_hE_eZ`, `giambelli` | Giambelli for the tableau Schur polynomials `schurV` | ac695b1 (#180) |
| `dualSymbol`, `hePair_dualSymbol` | a normalised symbol gives an `(h, e)` pair, `E(X) = 1/H(−X)` | edcba1c (#181) |
| `symbolOf`, `hePair_symbolOf`, `giambelli_toeplitz` | Giambelli for the Toeplitz minors of `c : ℕ → R`, `c₀ = 1` | 8057de4 (#182) |

## Roadmap: ThetaLiftsAsOneGiambelliDeterminant (RoadmapLab #9)

- **T3 (RMTlib).** Giambelli for the Toeplitz minors of the roadmap's symbol. It is done in general
  (`giambelli_toeplitz`). Once RH-Dual's T2 names the explicit symbol `c`, the remaining work is to
  instantiate `c` and check `c₀ = 1`.
- **Source.** P.-O. Dehaye, *Combinatorics of lower order terms in the moment conjectures for the Riemann
  zeta function*, arXiv:1201.4478, §7.1.4, eq. (55). That paper uses Giambelli in the Frobenius–Schur form of
  Olshanski–Regev–Vershik; RMTlib proves the classical Schur form.
- **Lean Pool.** The port is handled by the LeanPool session; the handoff note is
  `/data/grh/scratch/rmtlib/giambelli-handoff.md`.
