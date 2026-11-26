import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import RMTlib.BDTW.PatternA

/-!
# Node-4 positivity patterns: the Welch bound and its fermionic twin

RMTlib#36 (from RH-Dual's `bridge/links/node4-positivity.md`). Theorem S of Alpöge's proof (the
definite side) bounds a frame operator `Q = Σ_u γ_u B_u B_u*` on a `D`-dimensional space. Its exact
pieces are frame identities:

* **Welch bound** (`trace_sq_le_card_mul_trace_mul_self`): for symmetric `Q`,
  `(tr Q)² ≤ D · tr Q²`. `tr Q² = Σ_{ij} Q_ij² ≥ Σ_i Q_ii²`, then Cauchy–Schwarz on the diagonal.
  Equality (a tight frame, `Q` scalar) is not stated yet.
* **Fermionic twin** (`det_mul_transpose_eq_sum_sq`): `det (B Bᵀ) = Σ_{|S| = D} det(B_S)²`, which is
  pattern A of BDTW (`det_mul_diagonal_mul_transpose`) with the one-body weight `ρ ≡ 1`.

Both are tagged `@[frame_pattern]`, so the checker can read the corresponding sites of the proof as
`instance of` rows.
-/

namespace RMT.Positivity

open Matrix Finset

/-- **The Welch bound**: for a symmetric real `D × D` matrix, `(tr Q)² ≤ D · tr (Q Q)`. -/
@[frame_pattern]
theorem trace_sq_le_card_mul_trace_mul_self {D : ℕ} (Q : Matrix (Fin D) (Fin D) ℝ)
    (hQ : Qᵀ = Q) : (trace Q) ^ 2 ≤ D * trace (Q * Q) := by
  have hdiag : ∑ i, Q i i ^ 2 ≤ trace (Q * Q) := by
    rw [trace]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [diag_apply, Matrix.mul_apply]
    have hsym : ∀ j, Q i j * Q j i = Q i j ^ 2 := fun j => by
      have h := congrFun (congrFun hQ i) j
      rw [transpose_apply] at h
      rw [h, sq]
    simp_rw [hsym]
    exact Finset.single_le_sum (f := fun j => Q i j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin D))) (f := fun i => Q i i)
  rw [card_univ, Fintype.card_fin] at hcs
  calc (trace Q) ^ 2 = (∑ i, Q i i) ^ 2 := rfl
    _ ≤ D * ∑ i, Q i i ^ 2 := by exact_mod_cast hcs
    _ ≤ D * trace (Q * Q) := by gcongr

open Classical in
/-- **The fermionic twin** (Cauchy–Binet): `det (B Bᵀ) = Σ_S det(B_S)²`, over the `N`-element sets
`S` of columns. Pattern A with the one-body weight `ρ ≡ 1`. -/
@[frame_pattern]
theorem det_mul_transpose_eq_sum_sq {R : Type*} [CommRing R] {N : ℕ} {W : Type*} [Fintype W]
    [LinearOrder W] (B : Matrix (Fin N) W R) :
    det (B * Bᵀ) = ∑ f : {f : Fin N → W // StrictAnti f}, det (B.submatrix id f.1) ^ 2 := by
  have h := RMT.BDTW.det_mul_diagonal_mul_transpose (fun _ : W => (1 : R)) B B
  rw [diagonal_one, Matrix.mul_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [sq]

end RMT.Positivity
