import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Fin

open MvPolynomial Finset

namespace RMT.Fock

variable {σ : Type*}

/-- The Fischer (Bargmann–Fock) pairing on `ℚ[x_v]`, `⟨x^m, x^m⟩ = ∏ m_v!`. Same formula as the
RH formalisation's `Formalism.GradedWeylDivisibility.fockQ`. -/
noncomputable def fischer (f g : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ)

theorem fischer_eq_sum_of_subset (f g : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fischer f g = ∑ m ∈ S, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fischer
  apply Finset.sum_subset hS
  intro m _ hm
  rw [notMem_support_iff.mp hm]
  ring

theorem fischer_comm (f g : MvPolynomial σ ℚ) : fischer f g = fischer g f := by
  classical
  rw [fischer_eq_sum_of_subset f g (f.support ∪ g.support) subset_union_left,
    fischer_eq_sum_of_subset g f (f.support ∪ g.support) subset_union_right]
  exact sum_congr rfl fun m _ => by ring

theorem fischer_add_right (f g₁ g₂ : MvPolynomial σ ℚ) :
    fischer f (g₁ + g₂) = fischer f g₁ + fischer f g₂ := by
  unfold fischer
  simp only [coeff_add, mul_add, add_mul, sum_add_distrib]

theorem fischer_add_left (f₁ f₂ g : MvPolynomial σ ℚ) :
    fischer (f₁ + f₂) g = fischer f₁ g + fischer f₂ g := by
  rw [fischer_comm, fischer_add_right, fischer_comm g, fischer_comm g]

theorem fischer_sum_left {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ)
    (g : MvPolynomial σ ℚ) : fischer (∑ i ∈ s, F i) g = ∑ i ∈ s, fischer (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [fischer]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, fischer_add_left, ih]

theorem fischer_C_mul_right (f g : MvPolynomial σ ℚ) (a : ℚ) :
    fischer f (C a * g) = a * fischer f g := by
  unfold fischer
  simp only [coeff_C_mul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem fischer_monomial_monomial [DecidableEq σ] (s t : σ →₀ ℕ) (a b : ℚ) :
    fischer (monomial s a) (monomial t b) =
      if s = t then a * b * ((∏ k ∈ s.support, (s k).factorial : ℕ) : ℚ) else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [fischer]
  · rw [fischer_eq_sum_of_subset _ _ {s} (by rw [support_monomial, if_neg ha]), sum_singleton,
      coeff_monomial, coeff_monomial, if_pos rfl]
    by_cases hst : s = t
    · subst hst; simp
    · rw [if_neg (Ne.symm hst), if_neg hst]; ring

theorem prod_factorial_single_add [DecidableEq σ] (s : σ →₀ ℕ) (v : σ) :
    (∏ k ∈ (Finsupp.single v 1 + s : σ →₀ ℕ).support, ((Finsupp.single v 1 + s : σ →₀ ℕ) k).factorial) =
      (s v + 1) * ∏ k ∈ s.support, (s k).factorial := by
  have key : ∀ (m : σ →₀ ℕ) (S : Finset σ), m.support ⊆ S →
      ∏ k ∈ m.support, (m k).factorial = ∏ k ∈ S, (m k).factorial := by
    intro m S hS
    apply prod_subset hS
    intro k _ hk
    rw [Finsupp.notMem_support_iff.mp hk, Nat.factorial_zero]
  have h1 : (Finsupp.single v 1 + s : σ →₀ ℕ).support ⊆ insert v s.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk
    rw [mem_insert, Finsupp.mem_support_iff]
    by_cases hkv : k = v
    · exact Or.inl hkv
    · right; simpa [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hkv] using hk
  rw [key _ _ h1, key s _ (subset_insert _ _)]
  have hv : v ∈ insert v s.support := mem_insert_self _ _
  rw [← mul_prod_erase _ _ hv, ← mul_prod_erase _ (fun k => (s k).factorial) hv]
  have h3 : ∏ k ∈ (insert v s.support).erase v, ((Finsupp.single v 1 + s : σ →₀ ℕ) k).factorial =
      ∏ k ∈ (insert v s.support).erase v, (s k).factorial := by
    refine prod_congr rfl fun k hk => ?_
    have hkv : k ≠ v := ne_of_mem_erase hk
    simp [Ne.symm hkv]
  rw [h3, Finsupp.add_apply, Finsupp.single_eq_same, add_comm 1 (s v), Nat.factorial_succ, mul_assoc]

theorem fischer_X_mul_monomial [DecidableEq σ] (v : σ) (s t : σ →₀ ℕ) (a b : ℚ) :
    fischer (X v * monomial s a) (monomial t b) = fischer (monomial s a) (pderiv v (monomial t b)) := by
  rw [X, monomial_mul, one_mul, pderiv_monomial, fischer_monomial_monomial, fischer_monomial_monomial]
  by_cases h : Finsupp.single v 1 + s = t
  · subst h
    have hs : Finsupp.single v 1 + s - Finsupp.single v 1 = s := add_tsub_cancel_left _ _
    rw [if_pos rfl, if_pos hs.symm, prod_factorial_single_add, Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring
  · rw [if_neg h]
    by_cases h' : s = t - Finsupp.single v 1
    · rw [if_pos h']
      have htv : t v = 0 := by
        by_contra hne
        apply h
        rw [h', add_comm]
        exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hne))
      rw [htv]
      simp
    · rw [if_neg h']

/-- **Adjointness**: multiplication by `x_v` is adjoint to `∂/∂x_v` for the Fischer pairing. -/
theorem fischer_X_mul_left [DecidableEq σ] (v : σ) (P Q : MvPolynomial σ ℚ) :
    fischer (X v * P) Q = fischer P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    induction Q using MvPolynomial.induction_on' with
    | monomial t b => exact fischer_X_mul_monomial v s t a b
    | add q₁ q₂ h₁ h₂ => rw [map_add, fischer_add_right, fischer_add_right, h₁, h₂]
  | add p₁ p₂ h₁ h₂ => rw [mul_add, fischer_add_left, fischer_add_left, h₁, h₂]

theorem fischer_one_one : fischer (1 : MvPolynomial σ ℚ) 1 = 1 := by
  classical
  rw [fischer_eq_sum_of_subset _ _ {0} (by rw [← C_1, support_C]; split_ifs <;> simp)]
  simp

/-! ### The trace -/

variable {N : ℕ}

/-- `tr X = Σ_a X_aa` on `N × N` matrices. -/
noncomputable def trX (N : ℕ) : MvPolynomial (Fin N × Fin N) ℚ := ∑ a, X (a, a)

theorem pderiv_trX (a : Fin N) : pderiv (a, a) (trX N) = 1 := by
  rw [trX, map_sum]
  rw [Fintype.sum_eq_single a fun b hb => by
    rw [pderiv_X, Pi.single_apply, if_neg (by simpa using hb)]]
  rw [pderiv_X, Pi.single_eq_same]

/-- **`‖(tr X)^m‖²_Fock = m! · N^m`.** -/
theorem fischer_trX_pow (m : ℕ) :
    fischer (trX N ^ m) (trX N ^ m) = (m.factorial : ℚ) * (N : ℚ) ^ m := by
  induction m with
  | zero => simp [fischer_one_one]
  | succ m ih =>
    have hd : ∀ a : Fin N, pderiv (a, a) (trX N ^ (m + 1)) = C ((m + 1 : ℕ) : ℚ) * trX N ^ m := by
      intro a
      rw [Derivation.leibniz_pow, pderiv_trX, smul_eq_mul, mul_one, Nat.add_sub_cancel,
        nsmul_eq_mul, ← map_natCast C]
    calc fischer (trX N ^ (m + 1)) (trX N ^ (m + 1))
        = ∑ a : Fin N, fischer (X (a, a) * trX N ^ m) (trX N ^ (m + 1)) := by
          rw [pow_succ', trX, sum_mul, fischer_sum_left]
      _ = ∑ _a : Fin N, ((m + 1 : ℕ) : ℚ) * fischer (trX N ^ m) (trX N ^ m) :=
          sum_congr rfl fun a _ => by rw [fischer_X_mul_left, hd, fischer_C_mul_right]
      _ = ((m + 1).factorial : ℚ) * (N : ℚ) ^ (m + 1) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ih, Nat.factorial_succ]
          push_cast
          ring

end RMT.Fock
