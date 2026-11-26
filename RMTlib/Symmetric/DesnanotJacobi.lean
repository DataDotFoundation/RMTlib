import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The Desnanot–Jacobi identity (Lewis Carroll's condensation), and the Hankel Toda equation

For a square matrix `A` of size `n + 2` over a commutative ring, deleting the last two rows and
columns:

  `det A · det A[^{n,n+1}, ^{n,n+1}] = det A[^{n+1}, ^{n+1}] · det A[^n, ^n]
                                        − det A[^{n+1}, ^n] · det A[^n, ^{n+1}]`

(`Matrix.det_mul_det_submatrix_castAdd`). Mathlib (as pinned) has no form of it; the proof is the
classical one: the trailing `2 × 2` block of `adjugate A` has determinant `det A · det A₀₀`
(`Matrix.det_adjugate_trailing`), proved first for the generic matrix, whose determinant is not a
zero divisor (as in Mathlib's `Matrix.det_adjugate`), then specialised.

## The Hankel Toda equation

For a Hankel matrix `H_k = [g_{i+j}]_{i,j<k}` the four minors are `H_k`, `H_{k−1}`, and the two
minors whose last row (or column) is moved down by one, which coincide (`Matrix.hankel_toda`):

  `H_{k+2} H_k = H_{k+1} H″_{k+1} − (H′_{k+1})²`.

When `g` lies in a differential ring with `g_n′ = g_{n+1}`, `H′` and `H″` are the first and second
derivatives of `H` (only the last row survives differentiation), and this is the Toda equation
`τ_{k+1} τ_{k−1} = τ_k τ_k″ − τ_k′²` of Hall's ladder (#227, #248). That reading is checked exactly in
`toy_examples/scripts/toda_jt.py` (section A, C), not formalised here. With `g_n = h_{n+1}` the
Hankel matrix is the Jacobi–Trudi matrix of the square `k^k` with its rows reversed, and with
`g_n = e_{n+1}` it is the dual Jacobi–Trudi matrix of the same (self-conjugate) square: the
equation holds for any sequence, so the fermionic twin is the same theorem
(`toy_examples/docs/toda-jt.md`).
-/

open Finset

namespace Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The trailing `2 × 2` block of the adjugate, times `det A`, is `det A` times `det A · det A₀₀`
(`A₀₀` the leading `n × n` block): the identity before cancelling `det A`. -/
theorem det_mul_det_adjugate_trailing_aux (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    det A * det ((adjugate A).submatrix (Fin.natAdd n) (Fin.natAdd n)) =
      det A * (det A * det (A.submatrix (Fin.castAdd 2) (Fin.castAdd 2))) := by
  classical
  let X : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
    of fun i j => if (i : ℕ) < n then (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) R) i j
      else adjugate A i j
  have hX : det X = det ((adjugate A).submatrix (Fin.natAdd n) (Fin.natAdd n)) := by
    rw [← det_submatrix_equiv_self finSumFinEquiv X,
      ← fromBlocks_toBlocks (X.submatrix finSumFinEquiv finSumFinEquiv)]
    have h12 : (X.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ = 0 := by
      ext i j
      simp only [toBlocks₁₂, of_apply, submatrix_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, X, Fin.val_castAdd, i.2, ite_true, Matrix.zero_apply]
      rw [one_apply_ne]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have h11 : (X.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ = 1 := by
      ext i j
      simp only [toBlocks₁₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left, X,
        Fin.val_castAdd, i.2, ite_true]
      by_cases h : i = j
      · subst h; simp
      · rw [one_apply_ne, one_apply_ne h]
        exact fun h' => h (Fin.castAdd_injective _ _ h')
    have h22 : (X.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ =
        (adjugate A).submatrix (Fin.natAdd n) (Fin.natAdd n) := by
      ext i j
      simp [toBlocks₂₂, X]
    rw [h12, det_fromBlocks_zero₁₂, h11, h22, det_one, one_mul]
  have hY : X * A = of fun (i j : Fin (n + 2)) => if (i : ℕ) < n then A i j
      else (A.det • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) R)) i j := by
    ext i j
    simp only [Matrix.mul_apply, X, of_apply]
    split_ifs
    · rw [← Matrix.mul_apply, one_mul]
    · rw [← Matrix.mul_apply, adjugate_mul]
  have hdY : det (X * A) = det (A.submatrix (Fin.castAdd 2) (Fin.castAdd 2)) * det A ^ 2 := by
    rw [hY, ← det_submatrix_equiv_self finSumFinEquiv,
      ← fromBlocks_toBlocks (submatrix _ finSumFinEquiv finSumFinEquiv)]
    have h21 : (submatrix (of fun i j : Fin (n + 2) => if (i : ℕ) < n then A i j
        else (A.det • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) R)) i j)
          finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
      ext i j
      simp only [toBlocks₂₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Fin.val_natAdd, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul]
      rw [ite_eq_right (by omega), one_apply_ne, mul_zero]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    rw [h21, det_fromBlocks_zero₂₁]
    congr 1
    · congr 1
      ext i j
      simp [toBlocks₁₁]
    · have h22 : (submatrix (of fun i j : Fin (n + 2) => if (i : ℕ) < n then A i j
          else (A.det • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) R)) i j)
            finSumFinEquiv finSumFinEquiv).toBlocks₂₂ = A.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
        ext i j
        simp only [toBlocks₂₂, of_apply, submatrix_apply, finSumFinEquiv_apply_right,
          Fin.val_natAdd, Matrix.smul_apply, smul_eq_mul]
        rw [ite_eq_right (by omega)]
        by_cases h : i = j
        · subst h; simp
        · rw [one_apply_ne h, one_apply_ne (fun h' => h (Fin.natAdd_injective _ _ h'))]
      rw [h22, det_smul, det_one, Fintype.card_fin, mul_one]
  calc det A * det ((adjugate A).submatrix (Fin.natAdd n) (Fin.natAdd n))
      = det (X * A) := by rw [det_mul, hX, mul_comm]
    _ = det A * (det A * det (A.submatrix (Fin.castAdd 2) (Fin.castAdd 2))) := by
      rw [hdY]; ring

/-- **Jacobi's complementary-minor identity for the trailing `2 × 2` block of the adjugate**:
`det (adj A)[{n, n+1}] = det A · det A[< n]`. -/
theorem det_adjugate_trailing (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    det ((adjugate A).submatrix (Fin.natAdd n) (Fin.natAdd n)) =
      det A * det (A.submatrix (Fin.castAdd 2) (Fin.castAdd 2)) := by
  let A' := mvPolynomialX (Fin (n + 2)) (Fin (n + 2)) ℤ
  have hA' : det ((adjugate A').submatrix (Fin.natAdd n) (Fin.natAdd n)) =
      det A' * det (A'.submatrix (Fin.castAdd 2) (Fin.castAdd 2)) :=
    mul_left_cancel₀ (det_mvPolynomialX_ne_zero (Fin (n + 2)) ℤ)
      (det_mul_det_adjugate_trailing_aux A')
  let f := MvPolynomial.aeval (R := ℤ) fun p : Fin (n + 2) × Fin (n + 2) => A p.1 p.2
  have hf : f.mapMatrix A' = A := mvPolynomialX_mapMatrix_aeval ℤ A
  have h := congrArg f hA'
  rw [AlgHom.map_det, map_mul, AlgHom.map_det, AlgHom.map_det] at h
  simp only [AlgHom.mapMatrix_apply] at h hf
  rw [← submatrix_map, ← submatrix_map, ← AlgHom.mapMatrix_apply, AlgHom.map_adjugate,
    AlgHom.mapMatrix_apply, hf] at h
  exact h

/-- **The Desnanot–Jacobi identity** (Lewis Carroll's condensation), at the last two rows and
columns: `det A · det A[^{n,n+1}] = det A[^{n+1}] · det A[^n] − det A[^{n+1}, ^n] · det A[^n, ^{n+1}]`,
where `A[^r, ^c]` deletes row `r` and column `c` (`Fin.castSucc` deletes `n + 1`, and
`(Fin.last n).castSucc.succAbove` deletes `n`). -/
theorem det_mul_det_submatrix_castAdd (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    det A * det (A.submatrix (Fin.castAdd 2) (Fin.castAdd 2)) =
      det (A.submatrix Fin.castSucc Fin.castSucc) *
          det (A.submatrix (Fin.last n).castSucc.succAbove (Fin.last n).castSucc.succAbove) -
        det (A.submatrix Fin.castSucc (Fin.last n).castSucc.succAbove) *
          det (A.submatrix (Fin.last n).castSucc.succAbove Fin.castSucc) := by
  rw [← det_adjugate_trailing, det_fin_two]
  simp only [submatrix_apply]
  have h0 : (Fin.natAdd n (0 : Fin 2) : Fin (n + 2)) = (Fin.last n).castSucc := Fin.ext (by simp)
  have h1 : (Fin.natAdd n (1 : Fin 2) : Fin (n + 2)) = Fin.last (n + 1) := Fin.ext (by simp)
  rw [h0, h1]
  rw [adjugate_fin_succ_eq_det_submatrix A ((Fin.last n).castSucc) ((Fin.last n).castSucc),
    adjugate_fin_succ_eq_det_submatrix A (Fin.last (n + 1)) (Fin.last (n + 1)),
    adjugate_fin_succ_eq_det_submatrix A ((Fin.last n).castSucc) (Fin.last (n + 1)),
    adjugate_fin_succ_eq_det_submatrix A (Fin.last (n + 1)) ((Fin.last n).castSucc)]
  simp only [Fin.succAbove_last, Fin.val_castSucc, Fin.val_last]
  have e1 : ((-1 : R) ^ (n + n : ℕ)) = 1 := by rw [← two_mul, pow_mul]; simp
  have e2 : ((-1 : R) ^ (n + 1 + (n + 1) : ℕ)) = 1 := by rw [← two_mul, pow_mul]; simp
  have e3 : ((-1 : R) ^ (n + 1 + n : ℕ)) = -1 := by
    rw [show n + 1 + n = 2 * n + 1 by ring, pow_succ, pow_mul]; simp
  have e4 : ((-1 : R) ^ (n + (n + 1) : ℕ)) = -1 := by
    rw [show n + (n + 1) = 2 * n + 1 by ring, pow_succ, pow_mul]; simp
  rw [e1, e2, e3, e4]
  ring

/-! ## The Hankel Toda equation -/

/-- **The Toda equation of a Hankel determinant.** For any sequence `g`, with
`H_k = det [g_{i+j}]_{i,j<k}`, `H′_k` the same with the last column moved down by one, and `H″_k`
with the last row and column moved:
`H_{k+2} H_k = H_{k+1} H″_{k+1} − (H′_{k+1})²`. Desnanot–Jacobi at the last two rows and columns;
the two mixed minors agree by the symmetry of a Hankel matrix. -/
theorem hankel_toda (g : ℕ → R) (k : ℕ) :
    det (of fun i j : Fin (k + 2) => g (i + j)) * det (of fun i j : Fin k => g (i + j)) =
      det (of fun i j : Fin (k + 1) => g (i + j)) *
          det (of fun i j : Fin (k + 1) =>
            g ((Fin.last k).castSucc.succAbove i + (Fin.last k).castSucc.succAbove j)) -
        det (of fun i j : Fin (k + 1) => g (i + (Fin.last k).castSucc.succAbove j)) ^ 2 := by
  set q := (Fin.last k).castSucc.succAbove
  have h := det_mul_det_submatrix_castAdd (of fun i j : Fin (k + 2) => g (i + j))
  have hT : det ((of fun i j : Fin (k + 2) => g (i + j)).submatrix q Fin.castSucc) =
      det (of fun i j : Fin (k + 1) => g (i + q j)) := by
    rw [← det_transpose]
    congr 1
    ext i j
    simp [add_comm]
  have hT' : det ((of fun i j : Fin (k + 2) => g (i + j)).submatrix Fin.castSucc q) =
      det (of fun i j : Fin (k + 1) => g (i + q j)) := rfl
  rw [sq]
  nth_rw 1 [← hT']
  rw [← hT]
  exact h

end Matrix
