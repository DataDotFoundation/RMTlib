import RMTlib.Symmetric.DesnanotJacobi
import RMTlib.Symmetric.DualJacobiTrudi

/-!
# The Toda equation of the square `k^k`: Desnanot–Jacobi on Jacobi–Trudi

The Jacobi–Trudi matrix of the square `k^k`, `(h_{k−i+j})_{i,j<k}`, read with its rows reversed is
the Hankel matrix `(h_{i+j+1})_{i,j<k}` (`det_hankel_hE`); the dual Jacobi–Trudi matrix of the
same square, `(e_{k−i+j})`, is the Hankel matrix of the `e`'s (`det_hankel_eZ`). So the
Hankel Toda equation (`Matrix.hankel_toda`, Desnanot–Jacobi at the last two rows and columns)
is, for the Schur function of the square (`square_toda`, `square_toda_fermion`):

  `H_{k+2} H_k = H_{k+1} H″_{k+1} − (H′_{k+1})²`,   `H_k = ε_k s_{k^k}`, `ε_k = sign(rev)`.

With `h_n ↦ g_n(x) = Σ_m x^m/(m!(m+n)!)` (`g_n′ = g_{n+1}`), `H_k` is Hall's `τ_k` (#227), the
primes become `d/dx`, and this is the Toda chain across Hall's rungs (#248); the identification
of the primed minors with derivatives, and their Schur expansions
(`H′ ↔ s_{(k+1, k^{k−1})}`, `H″ ↔ s_{(k+2,k^{k−1})} + s_{(k+1,k+1,k^{k−2})}`), are checked exactly in
`toy_examples/scripts/toda_jt.py` §A, C. In Jacobi–Trudi orientation the deleted rows are the
first two and the deleted columns the last two; the corner Desnanot–Jacobi of the same matrix
is instead the T-system on rectangles (§B there).

The square is self-conjugate, so `e` and `h` give the same Schur function through dual
Jacobi–Trudi (`RMT.Symmetric.schurV_conjV_eq_eDet`): the fermionic twin is the same equation with
`e` (`square_toda_fermion`).
-/

open Finset Matrix

namespace RMT.Symmetric

variable {R : Type*} [CommRing R]

/-- The Jacobi–Trudi matrix of the square `k^k`, rows reversed, is the Hankel matrix of the
`h`'s: `det (h_{i+j+1}) = sign(rev) · s_{k^k}`. -/
theorem det_hankel_hE (a : ℕ → R) (m k : ℕ) :
    det (of fun i j : Fin k => hE a m ((i + j : ℕ) + 1)) =
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : R) * schurV a k m (fun _ => k) := by
  rw [schurV_eq_det a m _ (fun _ _ _ => le_rfl), ← det_permute]
  congr 1
  ext i j
  have h : ((Fin.rev i : ℕ) : ℤ) = k - 1 - i := by
    have := i.2
    rw [Fin.val_rev]
    omega
  simp only [of_apply, submatrix_apply, jtMat, Fin.revPerm_apply, id, h]
  congr 1
  push_cast
  ring

/-- The dual Jacobi–Trudi matrix of the square, rows reversed, is the Hankel matrix of the `e`'s. -/
theorem det_hankel_eZ (a : ℕ → R) (m k : ℕ) :
    det (of fun i j : Fin k => eZ a m ((i + j : ℕ) + 1)) =
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : R) *
        eDet a m (fun _ : Fin k => (k : ℤ)) := by
  rw [eDet, ← det_permute]
  congr 1
  ext i j
  have h : ((Fin.rev i : ℕ) : ℤ) = k - 1 - i := by
    have := i.2
    rw [Fin.val_rev]
    omega
  simp only [of_apply, submatrix_apply, Fin.revPerm_apply, id, h]
  congr 1
  push_cast
  ring

/-- **The Toda equation of the square, bosonic**: Desnanot–Jacobi on the Jacobi–Trudi matrix of
`(k+2)^{k+2}` (rows reversed), `H_k = det (h_{i+j+1})_{i,j<k} = ± s_{k^k}` (`det_hankel_hE`). -/
theorem square_toda (a : ℕ → R) (m k : ℕ) :
    det (of fun i j : Fin (k + 2) => hE a m ((i + j : ℕ) + 1)) *
        det (of fun i j : Fin k => hE a m ((i + j : ℕ) + 1)) =
      det (of fun i j : Fin (k + 1) => hE a m ((i + j : ℕ) + 1)) *
          det (of fun i j : Fin (k + 1) => hE a m
            (((Fin.last k).castSucc.succAbove i + (Fin.last k).castSucc.succAbove j : ℕ) + 1)) -
        det (of fun i j : Fin (k + 1) => hE a m
            ((i + (Fin.last k).castSucc.succAbove j : ℕ) + 1)) ^ 2 :=
  hankel_toda (fun n => hE a m ((n : ℤ) + 1)) k

/-- **The fermionic twin**: the same with the `e`'s, `det (e_{i+j+1}) = ± det (e_{k−i+j}) = ± s_{k^k}`
(`det_hankel_eZ`, dual Jacobi–Trudi; the square is self-conjugate). -/
theorem square_toda_fermion (a : ℕ → R) (m k : ℕ) :
    det (of fun i j : Fin (k + 2) => eZ a m ((i + j : ℕ) + 1)) *
        det (of fun i j : Fin k => eZ a m ((i + j : ℕ) + 1)) =
      det (of fun i j : Fin (k + 1) => eZ a m ((i + j : ℕ) + 1)) *
          det (of fun i j : Fin (k + 1) => eZ a m
            (((Fin.last k).castSucc.succAbove i + (Fin.last k).castSucc.succAbove j : ℕ) + 1)) -
        det (of fun i j : Fin (k + 1) => eZ a m
            ((i + (Fin.last k).castSucc.succAbove j : ℕ) + 1)) ^ 2 :=
  hankel_toda (fun n => eZ a m ((n : ℤ) + 1)) k

end RMT.Symmetric
