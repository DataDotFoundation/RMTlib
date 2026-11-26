import RMTlib.Symmetric.MayaMolien

/-!
# The q-factorial counts permutations by inversions (RMTlib#163, target 4)

`∑_{σ ∈ S_k} q^{inv σ} = ∏_{i < k} [i+1]_q = [k]_q!`, proved by inserting the first value: a
permutation of `Fin (k+1)` is a first value `a` together with a permutation `τ` of `Fin k`,
`σ = cons a (a.succAbove ∘ τ)`, and `inv σ = a + inv τ` (the first letter is inverted with exactly
the `a` smaller values, and `succAbove` is order-preserving).

With `share_eq` this reads the share of pieriCone as `1 / ∑_σ q^{inv σ}`: one over the number of
complete flags of `F_q^k`, counted by Bruhat cells (`q^{inv σ}` points in the cell of `σ`).
-/

open Finset

namespace RMT.Symmetric.MayaMolien

/-- The number of inversions of a word `f : Fin k → Fin m`. -/
def inv {k m : ℕ} (f : Fin k → Fin m) : ℕ :=
  ∑ i : Fin k, ∑ j : Fin k, if i < j ∧ f j < f i then 1 else 0

/-- Inversions of a word split into those of its first letter and those of the rest. -/
theorem inv_succ {k m : ℕ} (f : Fin (k + 1) → Fin m) :
    inv f = (∑ j : Fin k, if f j.succ < f 0 then 1 else 0) + inv (fun j : Fin k => f j.succ) := by
  unfold inv
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Fin.sum_univ_succ]; simp [Fin.succ_pos]
  · refine sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_succ]; simp [Fin.succ_lt_succ_iff]

/-- Post-composing with a strictly monotone map preserves inversions. -/
theorem inv_strictMono {k m m' : ℕ} (f : Fin k → Fin m) {s : Fin m → Fin m'} (hs : StrictMono s) :
    inv (s ∘ f) = inv f := by
  unfold inv; simp [hs.lt_iff_lt]

/-- A permutation of `Fin n` takes exactly `a` values below `a`. -/
theorem sum_lt_perm {n : ℕ} (τ : Equiv.Perm (Fin n)) (a : Fin (n + 1)) :
    (∑ j : Fin n, if (τ j).castSucc < a then 1 else 0) = (a : ℕ) := by
  rw [Equiv.sum_comp τ (fun v => if v.castSucc < a then 1 else 0)]
  simp only [Fin.lt_def, Fin.val_castSucc]
  rw [Fin.sum_univ_eq_sum_range (fun v => if v < (a : ℕ) then 1 else 0), sum_boole]
  have : (range n).filter (· < (a : ℕ)) = range a := by
    ext v; simp only [mem_filter, mem_range]; have := a.2; omega
  simp [this]

/-- The word `cons a (a.succAbove ∘ τ)` is injective. -/
theorem cons_succAbove_injective {n : ℕ} (a : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Function.Injective (Fin.cons a (a.succAbove ∘ τ) : Fin (n + 1) → Fin (n + 1)) := by
  rw [Fin.cons_injective_iff]
  exact ⟨fun ⟨j, hj⟩ => Fin.succAbove_ne a (τ j) hj,
    (Fin.succAbove_right_injective).comp τ.injective⟩

/-- Insert the first value: `(a, τ) ↦ cons a (a.succAbove ∘ τ)`. -/
noncomputable def insertFirst {n : ℕ} (p : Fin (n + 1) × Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (cons_succAbove_injective p.1 p.2))

theorem insertFirst_bijective (n : ℕ) : Function.Bijective (insertFirst (n := n)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun ⟨a, τ⟩ ⟨b, ρ⟩ h => ?_, by simp [Fintype.card_perm, Nat.factorial_succ]⟩
  have h0 := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ 0) h
  simp only [insertFirst, Equiv.ofBijective_apply, Fin.cons_zero] at h0
  subst h0
  refine Prod.ext rfl (Equiv.ext fun j => ?_)
  have hj := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ j.succ) h
  simp only [insertFirst, Equiv.ofBijective_apply, Fin.cons_succ, Function.comp_apply] at hj
  exact Fin.succAbove_right_injective hj

theorem inv_insertFirst {n : ℕ} (a : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    inv (insertFirst (a, τ)) = a + inv τ := by
  rw [inv_succ]
  simp only [insertFirst, Equiv.ofBijective_apply, Fin.cons_zero, Fin.cons_succ,
    Function.comp_apply, Fin.succAbove_lt_iff_castSucc_lt]
  rw [sum_lt_perm]
  congr 1
  exact inv_strictMono (fun j => τ j) (Fin.strictMono_succAbove a)

/-- **The q-factorial is the inversion generating function of `S_k`.** -/
theorem sum_perm_pow_inv {R : Type*} [CommSemiring R] (q : R) (k : ℕ) :
    ∑ σ : Equiv.Perm (Fin k), q ^ inv σ = ∏ i ∈ range k, ∑ j ∈ range (i + 1), q ^ j := by
  induction k with
  | zero => simp [inv]
  | succ n ih =>
    rw [← Function.Bijective.sum_comp (insertFirst_bijective n), Fintype.sum_prod_type]
    simp only [inv_insertFirst, pow_add, ← mul_sum, ← sum_mul, ih, prod_range_succ]
    rw [mul_comm, Fin.sum_univ_eq_sum_range (fun j => q ^ j)]

/-- **pieriCone's share is one over the number of complete flags**, counted by Bruhat cells:
`q^{-C(k,2)} ∏_{i<k} (1 − q⁻¹)/(1 − q^{-(i+1)}) = (∑_{σ ∈ S_k} q^{inv σ})⁻¹`. -/
theorem share_eq_inv (q : ℝ) (hq : 1 < q) (k : ℕ) :
    q⁻¹ ^ (k * (k - 1) / 2) * ∏ i ∈ range k, (1 - q⁻¹) / (1 - q⁻¹ ^ (i + 1)) =
      (∑ σ : Equiv.Perm (Fin k), q ^ inv σ)⁻¹ := by
  rw [share_eq hq k, sum_perm_pow_inv]

end RMT.Symmetric.MayaMolien
