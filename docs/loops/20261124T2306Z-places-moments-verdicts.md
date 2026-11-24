# Loop 1: RMTlib.Moments through the places frame (verdicts)

Verdicts on `20261124T2256Z-places-moments-predictions.md`. All five checks exit 0: in RMTlib `lake build --wfail` and `lake test`, in MeaningLib `lake build --wfail`, `lake test` and the self-test. Tags: **proved** (Lean, standard axioms), **computed** (a run in this loop), **inferred**.

| | Prediction | Verdict | Tag |
|---|---|---|---|
| PL1 | (0.75) the frame reads nothing in Moments as written | **held** | computed |
| PL2 | (0.7) the restatement is proved in at most 80 lines | **held** | proved |
| PL3 | (0.6) one well-typed twin per restated theorem, no witness | **held after two corrections** | computed |
| PL4 | (0.8) the twin holds for `M ≤ 1`, all `k`; fails at `M = 2` for `k ≥ 2` | **held as promised; general `k ≥ 2` not proved** | proved, inferred |
| PL5 | (0.85) the metric does not move | **held** | proved |
| PL6 | (0.5) self-test and report each under 60 s | **held** | computed |

## Details

**PL1.**
- The report read 0 of the 64 theorems under `RMT.UN`, and 0 of the 372 under `RMT.Symmetric`.
- The cause: RMTlib writes the archimedean content as an anonymous `fun z => N + z`, never as a named constant. A frame that matches constants cannot see it.

**PL2.** `momentPoly_eq_contentProd` with its helpers takes 48 lines: the `square` diagram, `card_square`, `prod_weights_map`, and the reindexing by `Fin.rev`.

**PL3.** The first runs failed, and both failures were real defects:
1. `finContent` had lost its unused `[CommRing R]` argument, so substituting it for `archContent` was ill-typed. RMTlib was fixed: `finContent` now keeps the argument.
2. MeaningLib's new binding check then flagged a difference that was only in universe names. MeaningLib was fixed: types are compared up to renaming of universe parameters.

After the fixes: 2 theorems read, 2 twins proposed, 0 witnesses. Both proposals are false:
- the twin of `momentPoly_eq_contentProd`, by `twinPoly_coeff_two_ne`;
- the twin of `theorem3_iff_contentProd` at `(2, 2)`, by `not_theorem3_and_twin_two_two` together with the `#guard` check of Theorem 3 there.

The report decides nothing about truth, as intended.

**PL4.**
- Proved:
  - `twinPoly_coeff_eq`: for `M ≤ 1` and every `k`, because `Σ w = k³` (`weights_sum_eq`);
  - `theorem3Twin_le_one`: for every `k ≥ 1`;
  - `twinPoly_coeff_two_ne`: at `k = 2`, `24/12 ≠ 23/12`;
  - `not_theorem3_and_twin_two_two`.
- Not proved: the failure for every `k ≥ 2` is inferred. When `Σ c = 0`, the two values of `e₂` differ by `−Σ c²/2`. Over the square, `Σ c² = k²(k² − 1)/6`, which is positive for `k ≥ 2`.

**PL5.** Theorem 3 is still proved only for `M ≤ 1`.

**PL6.** The RMTlib report takes 5.6 s and the MeaningLib self-test 1.5 s.

## What the loop produced

1. **The frontier, explained** (proved for `M ≤ 1`; inferred beyond).
   - Theorem 3 is proved exactly where the finite-place twin, the content-free product `(X + k)^{k²}`, already gives the right coefficients.
   - `M = 2` is the first order at which the contents of the square matter, through their second moment `Σ c²`.
   - This is a Casimir-type quantity, the content sum that `RMT.Symmetric.omegaCasimir` already tracks.
2. **The `M = 2` target in closed form** (inferred; checked by hand at `k = 2` and `k = 3`):

   `exactCoeff k 2 = (C(k², 2)·k² − k²(k² − 1)/12) / ∏ w`

   - At `k = 2`: `24 − 1 = 23`.
   - At `k = 3`: `324 − 6 = 318`, which matches `((Σ w)² − Σ w²)/2 = (729 − 93)/2`.

   This turns "prove Theorem 3 at `M = 2`" into evaluating `thm3Coeff k 2` against an explicit right-hand side. The twin supplies the main term, and the second content moment supplies the correction.
3. **Two defects found by use, fixed in MeaningLib.** The report now checks the binding before reading, and an `unknown` carries the type checker's reason.

## Next loop, proposed

- **Frame:** places, extended with a role for the second content moment. Twin plus correction: `finContent` together with a `Σ c²` term.
- **Target:** prove the closed form above for `exactCoeff k 2` (pure algebra: Vieta and `Σ c²` over the square). Then attack `thm3Coeff k 2`.
- **Metric:** the range of `M` proved.
