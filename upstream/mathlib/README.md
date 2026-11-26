# Mathlib-ready candidates (prepared, not opened)

These files restate RMTlib lemmas that the condensed RH edition also proves, in Mathlib style:
Mathlib namespaces, minimal imports, docstrings, no RMTlib dependency. The aim is for the edition
(and upstream) to rely on Mathlib rather than on RMTlib.

**Status: not submitted.** Mathlib requires disclosure of AI assistance, and a PR needs a human
contributor who engages with review. The owner decides whether, and by whom, these are opened. The
`<contributor>` placeholders in the headers are left for that person.

| File | Declarations | RMTlib source | Condensed-edition counterpart |
|---|---|---|---|
| `Factorization_Log.lean` | `Real.log_natCast_eq_sum_factorization`, `Real.sum_factorization_mul_log_le`, `Real.sum_padicValNat_mul_log_le` | `RMT.Transfer.log_eq_sum`, `sum_log_mul_padicValNat_le`, `sum_padicValNat_mul_log_le` (#140, #159) | `New.Selmer.sum_padicValNat_mul_log_le` |
| `Determinant_Interlacing.lean` | `Matrix.det_threshold`, `Matrix.det_interlacing_indicator` | `RMT.Symmetric.det_threshold`, `det_interlacing_indicator` (#161, #162) | `New.UpperBound.ElementaryDivisors.det_interlacing_indicator` |

Changes from the RMTlib versions:
- **Factorization:** the core inequality is stated with `Nat.factorization` over *any* `Finset ℕ`, with no
  primality or `n ≠ 0` hypothesis; non-primes have factorization `0`. The `padicValNat` form is a
  corollary.
- **Determinant:** helpers are `private`, `induction'` is gone, and `one_ne_zero` is avoided because
  `R` may be trivial.

**Check** (not part of `lake build`):
`lake env lean upstream/mathlib/<File>.lean`. Both files compile against RMTlib's Mathlib pin and
pass `#lint` (15 linters) as of 2026-11-26. Before opening, re-check against Mathlib `master`, and
choose final locations (e.g. `Mathlib/Analysis/SpecialFunctions/Log/` and
`Mathlib/LinearAlgebra/Matrix/Determinant/`).

Pending (RH-Dual#246): `share_eq` / `sum_perm_pow_inv`, if the edition's shortening estimate shows a
real saving.
