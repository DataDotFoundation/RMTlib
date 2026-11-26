import RMTlib.Fock.Columns
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Factorial.BigOperators
import MeaningLib.Frame.Pattern

/-!
# The Fock norm of a one-row Schur function

For an `N × N` matrix of variables `X`, the Schur function of the one-row shape `(k)` is `h_k(X)`,
the trace of `X` acting on `Sym^k(ℚ^N)` (`hX`). In the monomial basis `y^α` (`|α| = k`) of
`Sym^k`, `X` sends `y_i ↦ Σ_j x_{ji} y_j`, so the coefficient of `x^M` in the trace is
`∏_i α_i! / ∏_{i,j} M_{ij}!`, summed over the matrices `M` whose row and column sums are both `α`.

Its Fischer (Fock) norm is

  `‖h_k(X)‖²_Fock = N (N + 1) ⋯ (N + k − 1) = ∏_{(0, j) ∈ (k)} (N + j)`,

the content product `∏ (N + c)` of the row, with contents `0, 1, …, k − 1` (`fischer_hX`,
`fischer_hX_contentProd`). This is the one-row case of the content-twisted Hall pairing.

**Rows and columns.** The column `(1^k)` gives `∏ (N − i)` (`RMT.Fock.fischer_eX_contentProd`).
The two shapes are transposes of each other, their contents are negatives of each other, and so
are the two norms up to `N ↦ −N`: `‖h_k‖²(N) = (−1)^k ‖e_k‖²(−N)` as polynomials in `N`
(`fischer_hX_eq_neg_eX`). This is the `ω` duality between `Sym` and `Λ` read on the Fock side, as
the negation of contents (`RMT.Symmetric.contentProd_transpose`).

**The count.** For fixed `α`, `Σ_M (∏ α!)² / ∏ M! = ∏ α! · Σ_M ∏_i multinomial(M i)`, and the
last sum is the multinomial coefficient of `α` (`sum_prod_multinomial`, by comparing coefficients
in `(Σ_j y_j)^k = ∏_i (Σ_j y_j)^{α_i}`). So each `α` contributes `k!`, and there are
`C(N + k − 1, k)` of them.

## Main results

* `sum_prod_multinomial`: `Σ_{M, row sums a, column sums b} ∏_i multinomial(M i) = multinomial b`.
* `fischer_hX`: `‖h_k(X)‖² = N.ascFactorial k`.
* `fischer_hX_contentProd`: the same, as the content product of the row.
* `fischer_hX_eq_neg_eX`: rows and columns exchanged by `N ↦ −N`.
-/

open MvPolynomial Finset

namespace RMT.Fock

variable {N : ℕ}

/-- The monomial `y^v` in `ℕ[y_1, …, y_N]`. -/
theorem prod_X_pow (v : Fin N → ℕ) :
    (∏ j, X j ^ v j : MvPolynomial (Fin N) ℕ) = monomial (Finsupp.equivFunOnFinite.symm v) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp

theorem sum_X_pow (n : ℕ) :
    (∑ j, X j : MvPolynomial (Fin N) ℕ) ^ n
      = ∑ v ∈ Nat.antidiagonalTuple N n,
          monomial (Finsupp.equivFunOnFinite.symm v) (Nat.multinomial univ v) := by
  rw [sum_pow_eq_sum_piAntidiag, piAntidiag_univ_fin_eq_antidiagonalTuple]
  refine sum_congr rfl fun v _ => ?_
  rw [prod_X_pow, ← map_natCast (C : ℕ →+* MvPolynomial (Fin N) ℕ), C_mul_monomial, mul_one]
  rfl

theorem sum_prod_multinomial (a b : Fin N → ℕ) (hab : ∑ i, b i = ∑ i, a i) :
    ∑ M ∈ (Fintype.piFinset fun i => Nat.antidiagonalTuple N (a i)).filter
        (fun M => ∀ j, ∑ i, M i j = b j), ∏ i, Nat.multinomial univ (M i)
      = Nat.multinomial univ b := by
  have key := congrArg (fun p : MvPolynomial (Fin N) ℕ => p.coeff (Finsupp.equivFunOnFinite.symm b))
    (prod_pow_eq_pow_sum univ a (∑ j, X j : MvPolynomial (Fin N) ℕ))
  simp_rw [sum_X_pow, prod_univ_sum, ← monomial_sum_prod, coeff_sum, coeff_monomial] at key
  rw [sum_ite, sum_const_zero, add_zero] at key
  rw [sum_eq_single_of_mem b (by simpa [Nat.mem_antidiagonalTuple] using hab)] at key
  · rw [if_pos rfl] at key
    rw [← key]
    refine sum_congr (filter_congr ?_) fun _ _ => rfl
    intro M _
    rw [Finsupp.ext_iff]
    simp [Finset.sum_apply]
  · intro v _ hv
    rw [if_neg]
    exact fun h => hv (Finsupp.equivFunOnFinite.symm.injective h)


variable (N) in
/-- The `N × N` matrices of naturals with row sums `a` and column sums `b`. -/
def margins (a b : Fin N → ℕ) : Finset (Fin N → Fin N → ℕ) :=
  (Fintype.piFinset fun i => Nat.antidiagonalTuple N (a i)).filter
    (fun M => ∀ j, ∑ i, M i j = b j)

/-- The exponent `x^M` of a matrix of naturals, `M i j` the power of `x_{ij}`. -/
noncomputable def matExp (M : Fin N → Fin N → ℕ) : Fin N × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun p : Fin N × Fin N => M p.1 p.2)

/-- The coefficient `∏_i (α i)! / ∏_{i,j} (M i j)!` of `x^M` in `h_k(X)`. -/
noncomputable def hCoeff (α : Fin N → ℕ) (M : Fin N → Fin N → ℕ) : ℚ :=
  ((∏ i, (α i).factorial : ℕ) : ℚ) / ((∏ i, ∏ j, (M i j).factorial : ℕ) : ℚ)

variable (N) in
/-- `h_k(X)`: the trace of the generic matrix on `Sym^k(ℚ^N)`, in the monomial basis. -/
noncomputable def hX (k : ℕ) : MvPolynomial (Fin N × Fin N) ℚ :=
  ∑ α ∈ Nat.antidiagonalTuple N k, ∑ M ∈ margins N α α, monomial (matExp M) (hCoeff α M)

theorem mem_margins {a b : Fin N → ℕ} {M : Fin N → Fin N → ℕ} :
    M ∈ margins N a b ↔ (∀ i, ∑ j, M i j = a i) ∧ ∀ j, ∑ i, M i j = b j := by
  simp [margins, Nat.mem_antidiagonalTuple]

theorem matExp_apply (M : Fin N → Fin N → ℕ) (i j : Fin N) : matExp M (i, j) = M i j := rfl

theorem matExp_injective : Function.Injective (matExp (N := N)) := by
  intro M M' h
  funext i j
  exact congrArg (fun f => f (i, j)) h

theorem prod_factorial_matExp (M : Fin N → Fin N → ℕ) :
    (∏ v ∈ (matExp M).support, (matExp M v).factorial) = ∏ i, ∏ j, (M i j).factorial := by
  rw [prod_subset (subset_univ _) (fun v _ hv => by
    rw [Finsupp.notMem_support_iff.mp hv, Nat.factorial_zero]), Fintype.prod_prod_type]
  rfl

/-- Each term: `hCoeff² · ∏ M! = ∏ α! · ∏_i multinomial(M i)`. -/
theorem hCoeff_sq_mul {α : Fin N → ℕ} {M : Fin N → Fin N → ℕ} (hM : ∀ i, ∑ j, M i j = α i) :
    hCoeff α M ^ 2 * ((∏ i, ∏ j, (M i j).factorial : ℕ) : ℚ)
      = (((∏ i, (α i).factorial) * ∏ i, Nat.multinomial univ (M i) : ℕ) : ℚ) := by
  have hspec : (∏ i, (α i).factorial) = (∏ i, ∏ j, (M i j).factorial) * ∏ i, Nat.multinomial univ (M i) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [Nat.multinomial_spec, hM]
  have hP : ((∏ i, ∏ j, (M i j).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  rw [hCoeff, hspec, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  field_simp

/-- For each `α`, the terms of `h_k(X)` indexed by matrices with both margins `α` contribute `k!`
to the norm. -/
theorem sum_margins_hCoeff (α : Fin N → ℕ) :
    ∑ M ∈ margins N α α, hCoeff α M ^ 2 * ((∏ i, ∏ j, (M i j).factorial : ℕ) : ℚ)
      = ((∑ i, α i).factorial : ℚ) := by
  rw [sum_congr rfl fun M hM => hCoeff_sq_mul (mem_margins.mp hM).1, ← Nat.cast_sum, ← mul_sum,
    show ∑ M ∈ margins N α α, ∏ i, Nat.multinomial univ (M i) = Nat.multinomial univ α from
      sum_prod_multinomial α α rfl, Nat.multinomial_spec]

theorem card_antidiagonalTuple (k : ℕ) : #(Nat.antidiagonalTuple N k) = (N + k - 1).choose k := by
  rw [← piAntidiag_univ_fin_eq_antidiagonalTuple,
    show #(piAntidiag (univ : Finset (Fin N)) k) = #(finsuppAntidiag (univ : Finset (Fin N)) k) by
      simp [finsuppAntidiag], card_finsuppAntidiag_nat_eq_choose, card_univ, Fintype.card_fin]

/-- **The Fock norm of `h_k(X)`** is `N (N + 1) ⋯ (N + k − 1)`. -/
theorem fischer_hX (k : ℕ) : fischer (hX N k) (hX N k) = (N.ascFactorial k : ℚ) := by
  classical
  have hsum : hX N k = ∑ p ∈ (Nat.antidiagonalTuple N k).sigma (fun α => margins N α α),
      monomial (matExp p.2) (hCoeff p.1 p.2) := by
    rw [hX, sum_sigma]
  have hinj : Set.InjOn (fun p : (Σ _ : Fin N → ℕ, Fin N → Fin N → ℕ) => matExp p.2)
      (((Nat.antidiagonalTuple N k).sigma (fun α => margins N α α)) : Set _) := by
    rintro ⟨α, M⟩ hp ⟨β, M'⟩ hq h
    obtain rfl : M = M' := matExp_injective h
    have hα := (mem_margins.mp (mem_sigma.mp hp).2).1
    have hβ := (mem_margins.mp (mem_sigma.mp hq).2).1
    obtain rfl : α = β := funext fun i => (hα i).symm.trans (hβ i)
    rfl
  rw [hsum, fischer_sum_monomial _ _ _ hinj]
  simp_rw [prod_factorial_matExp]
  rw [sum_sigma, sum_congr rfl fun α hα => by
    rw [sum_margins_hCoeff, Nat.mem_antidiagonalTuple.mp hα], sum_const, card_antidiagonalTuple,
    Nat.ascFactorial_eq_factorial_mul_choose', nsmul_eq_mul]
  push_cast
  ring

/-- **The Fock norm of `h_k(X)` is the content product `∏ (N + c)` of the row `(k)`**, whose
cells `(0, j)` have contents `j`. -/
@[frame_pattern]
theorem fischer_hX_contentProd (k : ℕ) :
    fischer (hX N k) (hX N k)
      = ((RMT.Symmetric.contentProdP (fun z : ℤ => (N : ℤ) + z) [k] : ℤ) : ℚ) := by
  rw [fischer_hX, RMT.Symmetric.contentProdP, Nat.ascFactorial_eq_prod_range]
  simp

/-- **Rows and columns are exchanged by `N ↦ −N`**: the content product `∏ (N + c)` of the row
`(k)`, which is `‖h_k(X)‖²_Fock`, is `(−1)^k` times that of the column `(1^k)`, which is
`‖e_k(X)‖²_Fock`, with `N` replaced by `−N`. Transposing negates contents. -/
@[frame_pattern]
theorem fischer_hX_eq_neg_eX (k : ℕ) :
    RMT.Symmetric.contentProdP (fun z : ℤ => (N : ℤ) + z) [k]
      = (-1) ^ k * RMT.Symmetric.contentProdP (fun z : ℤ => -(N : ℤ) + z) (List.replicate k 1) := by
  have hcol : RMT.Symmetric.contentProdP (fun z : ℤ => -(N : ℤ) + z) (List.replicate k 1)
      = ∏ i ∈ range k, (-(N : ℤ) - i) := by
    rw [RMT.Symmetric.contentProdP, List.length_replicate]
    refine prod_congr rfl fun i hi => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (mem_range.mp hi)]
    simp [sub_eq_add_neg]
  have hrow : RMT.Symmetric.contentProdP (fun z : ℤ => (N : ℤ) + z) [k]
      = ∏ j ∈ range k, ((N : ℤ) + j) := by
    simp [RMT.Symmetric.contentProdP]
  rw [hcol, hrow, show ((-1 : ℤ) ^ k) = ∏ _i ∈ range k, (-1 : ℤ) by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  ring

end RMT.Fock
