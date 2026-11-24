import RMTlib.Fock.Laplacian
import RMTlib.Tableaux.Pieri

/-!
# Pieri's rule for `p₁` at the matrix level

For an `N × N` matrix of variables `X` and the Jacobi–Trudi Schur functions
`s_ν(X) = det (h_{ν_i − i + j}(X))` (`RMT.Fock.sX`):

  `tr X · s_ν(X) = Σ_i s_{ν + e_i}(X)`   (`trX_mul_sX`),

for every integer vector `ν` of length `l + 1` whose last entry is `0` (so that the box added in
the last row is accounted for). Terms where `ν + e_i` is not a partition vanish
(`sX_addBox_eq_zero`).

**The proof is formal**: it uses no relation among the `h_k(X)` beyond `h_0 = 1`, `h_{<0} = 0` and
`h_1(X) = tr X`. So no MacMahon relation and no map `Λ → class functions` is needed
(`bridge/links/fock-norm.md` §6.3 expected one).
* The row of `ν + e_i` is row `i` of the Jacobi–Trudi matrix `A` of `ν`, shifted one column left.
  This is row `i` of `A S`, for the trace-free shift `S`, plus a correction `v_i = h_{ν_i − i + l + 1}`
  in the last column.
* Summed over `i`, the `A S` rows give `tr S · det A = 0` (`RMT.Fock.sum_det_updateRow_mul`, as for
  `RMT.Fock.trD_sX`).
* The last row of `A` is the unit vector `e_l`, because `ν_l = 0`. So a correction in row `i ≠ l`
  makes row `i` proportional to the last row, and the determinant vanishes. The correction in the
  last row is `v_l = h_1 = tr X`, and gives `tr X · det A`.

## Main results

* `trX_mul_sX`: **`tr X · s_ν(X) = Σ_i s_{ν+e_i}(X)`**.
* `sX_addBox_eq_zero`: adding a box that is not addable gives `0` (two equal rows).

Used in `RMTlib.Fock.Diagonal` for the Fock diagonal of every shape.
-/

open MvPolynomial Finset

namespace RMT.Fock

variable {N : ℕ}

theorem hZ_one : hZ N 1 = trX N := by
  simp [hZ, hX_one]

/-- The last row of the Jacobi–Trudi matrix of `ν` with `ν_l = 0` is the unit vector `e_l`. -/
theorem jt_last_row {l : ℕ} (lam : Fin (l + 1) → ℤ) (hl : lam (Fin.last l) = 0) (j : Fin (l + 1)) :
    hZ N (lam (Fin.last l) - (Fin.last l : ℕ) + j) =
      (Pi.single (Fin.last l) 1 : Fin (l + 1) → MvPolynomial (Fin N × Fin N) ℚ) j := by
  rw [hl]
  by_cases hj : j = Fin.last l
  · subst hj
    simp [hZ, hX_zero]
  · rw [Pi.single_apply, if_neg hj, hZ, if_neg]
    have := Fin.val_lt_last hj
    simp only [Fin.val_last]
    omega

/-- **Pieri's rule for `p₁` at the matrix level**: `tr X · s_ν(X) = Σ_i s_{ν + e_i}(X)` for every
integer vector `ν` of length `l + 1` with `ν_l = 0`. -/
theorem trX_mul_sX {l : ℕ} (lam : Fin (l + 1) → ℤ) (hl : lam (Fin.last l) = 0) :
    trX N * sX N lam = ∑ i, sX N (Function.update lam i (lam i + 1)) := by
  classical
  set A : Matrix (Fin (l + 1)) (Fin (l + 1)) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun i j : Fin (l + 1) => hZ N (lam i - i + j)
  -- the trace-free shift: `(A S)_{ij} = A_{i, j+1}`
  set S : Matrix (Fin (l + 1)) (Fin (l + 1)) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun a b => if (a : ℕ) = b + 1 then 1 else 0
  set v : Fin (l + 1) → MvPolynomial (Fin N × Fin N) ℚ := fun i => hZ N (lam i - i + (l + 1))
  have hrow : ∀ i, (fun j : Fin (l + 1) => hZ N (lam i + 1 - i + j))
      = (A * S) i + v i • Pi.single (Fin.last l) 1 := by
    intro i
    funext j
    rw [Pi.add_apply, Matrix.mul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = Fin.last l
    · subst hj
      rw [sum_eq_zero fun a _ => by
        simp only [S, Matrix.of_apply]
        rw [if_neg (by have := a.isLt; simp only [Fin.val_last]; omega), mul_zero]]
      simp only [Pi.single_eq_same, mul_one, zero_add, v, Fin.val_last]
      congr 1
      ring
    · have hlt : (j : ℕ) + 1 < l + 1 := by have := Fin.val_lt_last hj; omega
      rw [sum_eq_single ⟨(j : ℕ) + 1, hlt⟩]
      · simp only [S, Matrix.of_apply, A, Pi.single_apply, if_neg hj, mul_zero, add_zero]
        rw [if_pos trivial, mul_one]
        congr 1
        push_cast
        ring
      · intro a _ ha
        simp only [S, Matrix.of_apply]
        rw [if_neg, mul_zero]
        intro h
        exact ha (Fin.ext h)
      · simp
  have hupd : ∀ i, A.updateRow i (fun j => hZ N (lam i + 1 - i + j))
      = Matrix.of fun i' j : Fin (l + 1) => hZ N (Function.update lam i (lam i + 1) i' - i' + j) := by
    intro i
    ext i' j
    by_cases h : i' = i
    · subst h; simp
    · simp [A, Matrix.updateRow_ne h, Function.update_of_ne h]
  have hlast : A (Fin.last l) = Pi.single (Fin.last l) 1 := by
    funext j
    exact jt_last_row lam hl j
  -- the corrections
  have hcorr : ∀ i, (A.updateRow i (v i • Pi.single (Fin.last l) 1)).det
      = if i = Fin.last l then trX N * A.det else 0 := by
    intro i
    rw [Matrix.det_updateRow_smul]
    split_ifs with h
    · subst h
      rw [← hlast, Matrix.updateRow_eq_self]
      simp only [v, Fin.val_last]
      rw [show lam (Fin.last l) - (l : ℤ) + (l + 1) = 1 by rw [hl]; ring, hZ_one]
    · rw [Matrix.det_zero_of_row_eq h (by rw [Matrix.updateRow_self, Matrix.updateRow_ne
        (Ne.symm h), hlast]), mul_zero]
  have hS : S.trace = 0 := by
    refine sum_eq_zero fun j _ => ?_
    simp [S]
  have hterm : ∀ i, sX N (Function.update lam i (lam i + 1))
      = (A.updateRow i ((A * S) i + v i • Pi.single (Fin.last l) 1)).det := by
    intro i
    rw [← hrow, hupd]
    rfl
  rw [sum_congr rfl fun i _ => hterm i]
  simp_rw [Matrix.det_updateRow_add]
  rw [sum_add_distrib, sum_det_updateRow_mul, hS, zero_mul, zero_add]
  simp_rw [hcorr]
  rw [sum_ite_eq', if_pos (mem_univ _)]
  rfl

/-- Adding a box to row `i` of a partition when the row above has the same length gives two equal
rows: the Schur function vanishes. -/
theorem sX_addBox_eq_zero {l : ℕ} {ν : Fin l → ℕ} (hν : Antitone ν) {i : Fin l}
    (hi : IsAddable ν i = false) :
    sX N (Function.update (fun k => (ν k : ℤ)) i ((ν i : ℤ) + 1)) = 0 := by
  classical
  have hpos : 0 < (i : ℕ) := by
    by_contra h0
    simp [IsAddable, h0] at hi
  simp only [IsAddable, dif_pos hpos, decide_eq_false_iff_not, not_lt] at hi
  set i' : Fin l := ⟨(i : ℕ) - 1, by omega⟩
  have hne : i' ≠ i := by simp [Fin.ext_iff, i']; omega
  have heq : ν i' = ν i := le_antisymm hi (hν (Fin.le_def.mpr (by simp [i'])))
  refine Matrix.det_zero_of_row_eq hne (funext fun j => ?_)
  simp only [Matrix.of_apply, Function.update_self, Function.update_of_ne hne, heq]
  congr 1
  simp only [i']
  push_cast [Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]
  ring

end RMT.Fock
