import RMTlib.Fock.Fischer
import RMTlib.Symmetric.WeightedCauchy
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import MeaningLib.Frame.Pattern

/-!
# The Fock norm of a one-column Schur function

For an `N × N` matrix of variables `X`, the Schur function of the one-column shape `(1^k)` is
`e_k(X)`, the sum of the principal `k × k` minors (`eX`). Its Fischer (Fock) norm is

  `‖e_k(X)‖²_Fock = N (N − 1) ⋯ (N − k + 1) = ∏_{(i, j) ∈ (1^k)} (N + (j − i))`,

the content product `∏ (N + c)` of the column (`fischer_eX`, `fischer_eX_contentProd`). This is
the one-column case of the content-twisted Hall pairing
`⟨s_λ(X), s_λ(X)⟩_Fock = ∏_{(i,j) ∈ λ} (N + j − i)` (see `RMTlib.Fock.ClassFunction`, where the
general statement is checked numerically and the power-sum case `p₁^m` is proved).

The contents of a column are `0, −1, …, −(k − 1)`: the norm is the product of `N + c` over them,
and it vanishes exactly when `k > N`, the cut of `contentProd_nat_add_eq_zero_iff`. The transposed
shape, the row `(k)`, has contents `0, 1, …, k − 1` and should give `N (N + 1) ⋯ (N + k − 1)`; that
case is not proved here.

The proof is a count. Distinct pairs (subset `S`, permutation of `S`) give distinct monomials, all
with coefficient `±1` and exponents `0` or `1`. So the Fischer norm of `e_k(X)` is the number of
such pairs, `C(N, k) · k!` (`fischer_sum_monomial`).

## Main results

* `fischer_sum_right`, `fischer_sum_monomial`: the Fischer norm of a sum of monomials with distinct
  exponents.
* `minor_eq`: a principal minor as a signed sum of squarefree monomials.
* `fischer_eX`: `‖e_k(X)‖² = N.descFactorial k`.
* `fischer_eX_contentProd`: the same, as the content product `∏ (N + c)` of the column.
-/

open MvPolynomial Finset

namespace RMT.Fock

variable {σ : Type*}

theorem fischer_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℚ)
    (F : ι → MvPolynomial σ ℚ) : fischer f (∑ i ∈ s, F i) = ∑ i ∈ s, fischer f (F i) := by
  rw [fischer_comm, fischer_sum_left]
  exact sum_congr rfl fun i _ => fischer_comm _ _

/-- **The Fischer norm of a sum of monomials with distinct exponents** is the sum of
`coefficient² · ∏ exponent!`. -/
theorem fischer_sum_monomial [DecidableEq σ] {ι : Type*} (I : Finset ι) (e : ι → σ →₀ ℕ)
    (c : ι → ℚ) (he : Set.InjOn e I) :
    fischer (∑ i ∈ I, monomial (e i) (c i)) (∑ i ∈ I, monomial (e i) (c i))
      = ∑ i ∈ I, c i ^ 2 * ((∏ k ∈ (e i).support, (e i k).factorial : ℕ) : ℚ) := by
  rw [fischer_sum_left]
  refine sum_congr rfl fun i hi => ?_
  rw [fischer_sum_right, sum_eq_single i]
  · rw [fischer_monomial_monomial, ite_eq_left rfl]
    ring
  · intro j hj hji
    rw [fischer_monomial_monomial, ite_eq_right]
    intro h
    exact hji (he hi hj h).symm
  · intro h
    exact absurd hi h

variable (N : ℕ)

/-- The generic `N × N` matrix `X = (x_{ij})`. -/
noncomputable def genMat : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) ℚ) :=
  Matrix.of fun i j => X (i, j)

/-- `e_k(X)`: the sum of the principal `k × k` minors of the generic matrix. It is the Schur
function of the one-column shape `(1^k)` evaluated at `X`. -/
noncomputable def eX (k : ℕ) : MvPolynomial (Fin N × Fin N) ℚ :=
  ∑ S ∈ powersetCard k (univ : Finset (Fin N)),
    ((genMat N).submatrix (fun i : S => i.1) (fun i : S => i.1)).det

variable {N}

/-- The exponent of the term of a minor indexed by the permutation `π` of `S`: one factor
`x_{π(i), i}` for each `i ∈ S`. -/
noncomputable def expo (S : Finset (Fin N)) (π : Equiv.Perm S) : Fin N × Fin N →₀ ℕ :=
  ∑ i : S, Finsupp.single ((π i).1, i.1) 1

/-- **A principal minor as a signed sum of monomials.** -/
theorem minor_eq (S : Finset (Fin N)) :
    ((genMat N).submatrix (fun i : S => i.1) (fun i : S => i.1)).det
      = ∑ π : Equiv.Perm S, monomial (expo S π) (((Equiv.Perm.sign π : ℤ) : ℚ)) := by
  rw [Matrix.det_apply']
  refine sum_congr rfl fun π _ => ?_
  rw [expo, monomial_sum_index]
  congr 1

theorem expo_apply (S : Finset (Fin N)) (π : Equiv.Perm S) (a b : Fin N) :
    expo S π (a, b) = if h : b ∈ S then (if (π ⟨b, h⟩).1 = a then 1 else 0) else 0 := by
  classical
  simp only [expo, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  split
  · rename_i h
    rw [Fintype.sum_eq_single ⟨b, h⟩]
    · simp [Prod.ext_iff]
    · intro i hi
      rw [ite_eq_right]
      intro he
      apply hi
      exact Subtype.ext (Prod.ext_iff.mp he).2
  · rename_i h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    intro he
    have hb : i.1 = b := (Prod.ext_iff.mp he).2
    exact h (hb ▸ i.2)

theorem expo_le_one (S : Finset (Fin N)) (π : Equiv.Perm S) (v : Fin N × Fin N) :
    expo S π v ≤ 1 := by
  obtain ⟨a, b⟩ := v
  rw [expo_apply]
  split_ifs <;> omega

/-- Distinct (subset, permutation) pairs give distinct monomials. -/
theorem expo_injective (k : ℕ) :
    Set.InjOn (fun p : (Σ S : Finset (Fin N), Equiv.Perm S) => expo p.1 p.2)
      (((powersetCard k (univ : Finset (Fin N))).sigma
        fun S => (univ : Finset (Equiv.Perm S))) : Set _) := by
  rintro ⟨S, π⟩ - ⟨T, ρ⟩ - h
  simp only at h
  have hST : S = T := by
    ext b
    constructor
    · intro hb
      have h1 := congrArg (fun f => f ((π ⟨b, hb⟩).1, b)) h
      simp only [expo_apply, dite_eq_left hb] at h1
      by_contra hbT
      rw [dite_eq_right hbT] at h1
      exact one_ne_zero h1
    · intro hb
      have h1 := congrArg (fun f => f ((ρ ⟨b, hb⟩).1, b)) h
      simp only [expo_apply, dite_eq_left hb] at h1
      by_contra hbS
      rw [dite_eq_right hbS] at h1
      exact zero_ne_one h1
  subst hST
  congr 1
  ext i
  have h1 := congrArg (fun f => f ((π i).1, i.1)) h
  simp only [expo_apply, dite_eq_left i.2, Subtype.coe_eta, ite_true] at h1
  by_contra hne
  split_ifs at h1 with hh
  exact hne (congrArg (fun x : S => ((x : Fin N) : ℕ)) (by simpa using hh.symm))

theorem prod_factorial_expo (S : Finset (Fin N)) (π : Equiv.Perm S) :
    (∏ v ∈ (expo S π).support, (expo S π v).factorial : ℕ) = 1 := by
  refine prod_eq_one fun v hv => ?_
  have h1 := expo_le_one S π v
  have h0 : expo S π v ≠ 0 := Finsupp.mem_support_iff.mp hv
  rw [show expo S π v = 1 by omega]
  rfl

/-- **The Fock norm of `e_k(X)`** is `N (N − 1) ⋯ (N − k + 1)`. -/
theorem fischer_eX (k : ℕ) : fischer (eX N k) (eX N k) = (N.descFactorial k : ℚ) := by
  classical
  have hsum : eX N k = ∑ p ∈ (powersetCard k (univ : Finset (Fin N))).sigma
      (fun S => (univ : Finset (Equiv.Perm S))),
      monomial (expo p.1 p.2) (((Equiv.Perm.sign p.2 : ℤ) : ℚ)) := by
    rw [eX, Finset.sum_sigma]
    exact sum_congr rfl fun S _ => minor_eq S
  rw [hsum, fischer_sum_monomial _ _ _ (expo_injective k)]
  have hterm : ∀ p : (Σ S : Finset (Fin N), Equiv.Perm S),
      (((Equiv.Perm.sign p.2 : ℤ) : ℚ)) ^ 2
        * ((∏ v ∈ (expo p.1 p.2).support, (expo p.1 p.2 v).factorial : ℕ) : ℚ) = 1 := by
    intro p
    rw [prod_factorial_expo]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p.2) with h | h <;> simp [h]
  simp only [hterm, sum_const, nsmul_eq_mul, mul_one, Finset.card_sigma, card_univ,
    Fintype.card_perm]
  rw [Finset.sum_congr rfl (g := fun _ => k.factorial) (fun S hS => by
    rw [Fintype.card_coe, (mem_powersetCard.mp hS).2]), sum_const, card_powersetCard,
    card_univ, Fintype.card_fin, smul_eq_mul, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- **The Fock norm of `e_k(X)` is the content product `∏ (N + c)` of the column `(1^k)`**,
whose cells `(i, 0)` have contents `−i`. -/
@[frame_pattern]
theorem fischer_eX_contentProd (k : ℕ) :
    fischer (eX N k) (eX N k)
      = ((RMT.Symmetric.contentProdP (fun z : ℤ => (N : ℤ) + z) (List.replicate k 1) : ℤ) : ℚ) := by
  rw [fischer_eX]
  have hc : RMT.Symmetric.contentProdP (fun z : ℤ => (N : ℤ) + z) (List.replicate k 1)
      = ∏ i ∈ range k, ((N : ℤ) - i) := by
    rw [RMT.Symmetric.contentProdP, List.length_replicate]
    refine prod_congr rfl fun i hi => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left (mem_range.mp hi)]
    simp [sub_eq_add_neg]
  rw [hc, Nat.descFactorial_eq_prod_range]
  rcases le_or_gt k N with hk | hk
  · push_cast
    refine prod_congr rfl fun i hi => ?_
    rw [Nat.cast_sub (le_of_lt (lt_of_lt_of_le (mem_range.mp hi) hk))]
  · have h0 : (∏ i ∈ range k, ((N : ℤ) - i)) = 0 :=
      prod_eq_zero (mem_range.mpr hk) (by simp)
    have h0' : (∏ i ∈ range k, (N - i)) = 0 :=
      prod_eq_zero (mem_range.mpr hk) (by simp)
    rw [h0, h0']
    simp

end RMT.Fock
