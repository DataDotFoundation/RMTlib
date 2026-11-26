import RMTlib.Fock.DehayeDelta

/-!
# Dehaye's `δ` is the `F` of a Weil `sl_2` (W2)

Companion to `bridge/links/virasoro-briefing.md` (§8); checks in `bridge/scripts/weil_cauchy.py`. GRH-free.

On two copies of the power-sum model (`RMT.Fock.DehayeDelta`), take the logarithm of the Cauchy kernel
`C = Σ_k p_k p̃_k / k` (`Ω = Σ_ν s_ν s̃_ν = exp C`) and Dehaye's `δ = Σ_k k ∂_{p_k} ∂_{p̃_k}`. Then
`[δ, C] = Σ_k (1 + p_k ∂_{p_k} + p̃_k ∂_{p̃_k})`. The number operators are unweighted, and the constant
counts the modes. With `u_k = p_k/√k`, each `k` is the unitary pair of `RMTlib.Fock.Weil` for one complex
variable: `(C, δ, H)` is the Weil `sl_2` of `(U(∞), U(1,1))`, **the pairs being the power-sum modes**.
Truncated at `K` (`CK`, `RMT.Fock.DehayeDelta.deltaK`, `HK`), the constant is `K − 1`:

* `deltaK_CK`: `[δ_K, C_K] = H_K = (K − 1) + Σ_{1≤k<K} (N_k + Ñ_k)`;
* `HK_CK`, `HK_deltaK`: `[H_K, C_K] = 2 C_K`, `[H_K, δ_K] = −2 δ_K`.

Against the twisted-diagonal `sl_2` `X_n = L_n ⊗ 1 − 1 ⊗ L̃_{−n}` at charges `(a, b)`:

* `CK_X1`: `[C_K, X_1] = −a p̃_1 + p_{K−1} p̃_K`;
* `CK_Xm1`: `[C_K, X_{−1}] = b p_1 − p_K p̃_{K−1}`;
* `CK_X0`: `[C_K, X_0] = 0`.

The last terms are truncation boundaries. Together with `RMT.Fock.DehayeDelta.delta_X1` etc., the Cauchy
`sl_2` and the twisted-diagonal `sl_2` commute **at charge 0**; at charge `a, b` the defects are the
Heisenberg modes `p̃_1, p_1` (and `α_1, α̃_1` for `δ`). ω ⊗ 1 sends `C_K` to the dual-Cauchy
`C^ω_K = Σ (−1)^{k−1} p_k p̃_k / k` (`omegaL_CK`), which with `δ^ω` has the same `H_K`
(`deltaOmK_COmK`).
-/

open MvPolynomial Finset
open RMT.Fock.DehayeDelta

namespace RMT.Fock.WeilCauchy

/-- `p_k p̃_k`. -/
noncomputable def pq (k : ℕ) : Λ₂ := X (Sum.inl k) * X (Sum.inr k)

/-- `C_K = Σ_{1≤k<K} p_k p̃_k / k`, the truncated logarithm of the Cauchy kernel. -/
noncomputable def CK (K : ℕ) : End₂ := ∑ k ∈ Ico 1 K, ((k : ℚ)⁻¹) • mulL (pq k)

/-- The number operator of the `k`-th mode on both copies: `p_k ∂_{p_k} + p̃_k ∂_{p̃_k}`. -/
noncomputable def Nk (k : ℕ) : End₂ := mulL (X (Sum.inl k)) * dL k + mulL (X (Sum.inr k)) * dR k

/-- `H_K = (K − 1) + Σ_{1≤k<K} N_k`. -/
noncomputable def HK (K : ℕ) : End₂ := (((K - 1 : ℕ) : ℚ)) • 1 + ∑ k ∈ Ico 1 K, Nk k

theorem dL_X (k j : ℕ) : pderiv (Sum.inl k) (X (Sum.inl j) : Λ₂) = if k = j then 1 else 0 := by
  rw [pderiv_X]; by_cases h : k = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem dR_X (k j : ℕ) : pderiv (Sum.inr k) (X (Sum.inr j) : Λ₂) = if k = j then 1 else 0 := by
  rw [pderiv_X]; by_cases h : k = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem dL_Xr (k j : ℕ) : pderiv (Sum.inl k) (X (Sum.inr j) : Λ₂) = 0 := by simp [pderiv_X]
theorem dR_Xl (k j : ℕ) : pderiv (Sum.inr k) (X (Sum.inl j) : Λ₂) = 0 := by simp [pderiv_X]

/-- Partial derivatives commute. -/
theorem pd_comm (u v : ℕ ⊕ ℕ) (G : Λ₂) : pderiv u (pderiv v G) = pderiv v (pderiv u G) := by
  have h : ⁅(pderiv u : Derivation ℚ Λ₂ Λ₂), pderiv v⁆ = 0 :=
    MvPolynomial.derivation_ext fun w => by
      rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
      simp only [Pi.single_apply]; split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℚ Λ₂ Λ₂ => D G) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using h2

@[simp] theorem pd_ite (u : ℕ ⊕ ℕ) (p : Prop) [Decidable p] :
    pderiv u (if p then (1 : Λ₂) else 0) = 0 := by split_ifs <;> simp

/-- **One mode**: `∂_{p_k} ∂_{p̃_k} (p_j p̃_j F) = p_j p̃_j ∂_{p_k} ∂_{p̃_k} F + [k = j] (1 + N_k) F`. -/
theorem dLdR_pq (k j : ℕ) (F : Λ₂) :
    dL k (dR k (pq j * F)) = pq j * dL k (dR k F) +
      if k = j then F + X (Sum.inl k) * dL k F + X (Sum.inr k) * dR k F else 0 := by
  simp only [dL, dR, pq, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, map_add, dL_X, dR_X,
    dL_Xr, dR_Xl, pd_ite, map_zero]
  by_cases h : k = j
  · subst h; simp; ring
  · simp [h]

/-- `N_k (p_j p̃_j F) = p_j p̃_j N_k F + 2 [k = j] p_j p̃_j F`. -/
theorem Nk_pq (k j : ℕ) (F : Λ₂) :
    Nk k (pq j * F) = pq j * Nk k F + if k = j then (2 : ℚ) • (pq j * F) else 0 := by
  simp only [Nk, LinearMap.add_apply, Module.End.mul_apply, mulL, LinearMap.mulLeft_apply, dL, dR,
    pq, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, dL_X, dR_X, dL_Xr, dR_Xl]
  by_cases h : k = j
  · subst h; simp [two_smul]; ring
  · simp [h]; ring

/-- `N_k ∂_{p_j} ∂_{p̃_j} F = ∂_{p_j} ∂_{p̃_j} N_k F − 2 [k = j] ∂_{p_j} ∂_{p̃_j} F`. -/
theorem Nk_dLdR (k j : ℕ) (F : Λ₂) :
    Nk k (dL j (dR j F)) = dL j (dR j (Nk k F)) - if k = j then (2 : ℚ) • dL j (dR j F) else 0 := by
  simp only [Nk, LinearMap.add_apply, Module.End.mul_apply, mulL, LinearMap.mulLeft_apply, dL, dR,
    Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, map_add, dL_X, dR_X, dL_Xr, dR_Xl,
    pd_ite, mul_zero, add_zero, zero_add]
  have hA : pderiv (Sum.inl j) (pderiv (Sum.inr j) (pderiv (Sum.inl k) F)) =
      pderiv (Sum.inl k) (pderiv (Sum.inl j) (pderiv (Sum.inr j) F)) := by
    rw [pd_comm (Sum.inr j) (Sum.inl k) F, pd_comm (Sum.inl j) (Sum.inl k) (pderiv (Sum.inr j) F)]
  have hB : pderiv (Sum.inl j) (pderiv (Sum.inr j) (pderiv (Sum.inr k) F)) =
      pderiv (Sum.inr k) (pderiv (Sum.inl j) (pderiv (Sum.inr j) F)) := by
    rw [pd_comm (Sum.inr j) (Sum.inr k) F, pd_comm (Sum.inl j) (Sum.inr k) (pderiv (Sum.inr j) F)]
  rw [hA, hB]
  by_cases h : k = j
  · subst h; simp [two_smul, pd_comm (Sum.inl k) (Sum.inr k)]; ring
  · simp [h, Ne.symm h]

/-! ## Operator form and the summed `sl_2` -/

theorem comm_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (A : ι → End₂) (B : κ → End₂) :
    (∑ i ∈ s, A i) * (∑ j ∈ t, B j) - (∑ j ∈ t, B j) * (∑ i ∈ s, A i) =
      ∑ i ∈ s, ∑ j ∈ t, (A i * B j - B j * A i) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := t)]
  simp only [← Finset.sum_sub_distrib]

theorem smul_sub' (c : ℚ) (A B : End₂) : c • A - c • B = c • (A - B) := (smul_sub c A B).symm

theorem smul_comm_smul (c d : ℚ) (A B : End₂) :
    (c • A) * (d • B) - (d • B) * (c • A) = (c * d) • (A * B - B * A) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm d c, smul_sub']

theorem T_pq (k j : ℕ) :
    (dL k * dR k) * mulL (pq j) - mulL (pq j) * (dL k * dR k) = if k = j then 1 + Nk k else 0 := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, mulL, LinearMap.mulLeft_apply, dLdR_pq]
  split_ifs with h
  · subst h; simp [Nk, mulL]; abel
  · simp

theorem Nk_mul_pq (k j : ℕ) :
    Nk k * mulL (pq j) - mulL (pq j) * Nk k = if k = j then (2 : ℚ) • mulL (pq j) else 0 := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, mulL, LinearMap.mulLeft_apply, Nk_pq]
  split_ifs with h <;> simp

theorem Nk_mul_dLdR (k j : ℕ) :
    Nk k * (dL j * dR j) - (dL j * dR j) * Nk k = if k = j then (-2 : ℚ) • (dL j * dR j) else 0 := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Nk_dLdR]
  split_ifs with h <;> simp [neg_smul]

theorem deltaK_eq_Ico (K : ℕ) : deltaK K = ∑ k ∈ Ico 1 K, (k : ℚ) • (dL k * dR k) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [deltaK]
  · rw [deltaK, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hK]; simp

theorem sum_Ico_ite (K : ℕ) (k : ℕ) (f : ℕ → End₂) :
    (∑ j ∈ Ico 1 K, if k = j then f j else 0) = if k ∈ Ico 1 K then f k else 0 := by
  rw [Finset.sum_ite_eq]

/-- **`[δ, C] = H`**: `[δ_K, C_K] = (K − 1) + Σ_{1≤k<K} (N_k + Ñ_k)`. -/
theorem deltaK_CK (K : ℕ) : deltaK K * CK K - CK K * deltaK K = HK K := by
  rw [deltaK_eq_Ico, CK, comm_sum_sum]
  simp only [smul_comm_smul, T_pq, smul_ite, smul_zero, sum_Ico_ite]
  rw [Finset.sum_ite_of_true (fun k hk => hk)]
  rw [Finset.sum_congr rfl fun k hk => by
    rw [mul_inv_cancel₀ (by have := (Finset.mem_Ico.mp hk).1; positivity), one_smul]]
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, HK, ← Nat.cast_smul_eq_nsmul ℚ]

/-- **`[H, C] = 2C`**. -/
theorem HK_CK (K : ℕ) : HK K * CK K - CK K * HK K = (2 : ℚ) • CK K := by
  rw [HK, add_mul, mul_add, show ∀ A B C D : End₂, A + B - (C + D) = (A - C) + (B - D) by
    intros; abel, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, sub_self, zero_add, CK]
  rw [comm_sum_sum]
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub', Nk_mul_pq, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ite_eq_left hj, smul_comm]

/-- **`[H, δ] = −2δ`**. -/
theorem HK_deltaK (K : ℕ) : HK K * deltaK K - deltaK K * HK K = (-2 : ℚ) • deltaK K := by
  rw [HK, add_mul, mul_add, show ∀ A B C D : End₂, A + B - (C + D) = (A - C) + (B - D) by
    intros; abel, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, sub_self, zero_add, deltaK_eq_Ico]
  rw [comm_sum_sum]
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub', Nk_mul_dLdR, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ite_eq_left hj, smul_comm]

/-! ## Against the twisted-diagonal `sl_2` -/

theorem mulL_add (g h : Λ₂) : mulL (g + h) = mulL g + mulL h := LinearMap.ext fun F => by simp [mulL, add_mul]
theorem mulL_neg (g : Λ₂) : mulL (-g) = -mulL g := LinearMap.ext fun F => by simp [mulL]
theorem mulL_smul (c : ℚ) (g : Λ₂) : mulL (c • g) = c • mulL g := LinearMap.ext fun F => by simp [mulL]
theorem mulL_C (c : ℚ) (g : Λ₂) : mulL (g * C c) = c • mulL g :=
  LinearMap.ext fun F => by simp [mulL, smul_eq_C_mul]; ring
theorem mulL_comm (g h : Λ₂) : mulL g * mulL h - mulL h * mulL g = 0 :=
  LinearMap.ext fun F => by simp [mulL]; ring

/-- `[g, D] = −D(g)` for a derivation `D`. -/
theorem mulL_der (D : Derivation ℚ Λ₂ Λ₂) (g : Λ₂) :
    mulL g * (D : End₂) - (D : End₂) * mulL g = -mulL (D g) := by
  rw [← der_comm_mul D g]; abel

theorem L1L_pq (a : ℚ) (k : ℕ) : L1L a (pq k) = X (Sum.inr k) * ((k : ℚ) • pcL a (k - 1)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [pq, L1L, Derivation.leibniz]
  · simp [pq, L1L, Derivation.leibniz, Nat.pos_iff_ne_zero.mp hk]

theorem upR_pq (k : ℕ) : upR (pq k) = X (Sum.inl k) * ((k : ℚ) • X (Sum.inr (k + 1))) := by
  simp [pq, upR, Derivation.leibniz]

theorem upL_pq (k : ℕ) : upL (pq k) = X (Sum.inr k) * ((k : ℚ) • X (Sum.inl (k + 1))) := by
  simp [pq, upL, Derivation.leibniz, mul_comm]

theorem L1R_pq (b : ℚ) (k : ℕ) : L1R b (pq k) = X (Sum.inl k) * ((k : ℚ) • pcR b (k - 1)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [pq, L1R, Derivation.leibniz]
  · simp [pq, L1R, Derivation.leibniz, Nat.pos_iff_ne_zero.mp hk]

theorem pq_X1 (a b : ℚ) (k : ℕ) :
    mulL (pq k) * X1 a b - X1 a b * mulL (pq k) = -mulL (L1L a (pq k)) + mulL (upR (pq k)) := by
  have h1 := mulL_der (L1L a) (pq k)
  have h2 := mulL_der upR (pq k)
  have h3 := mulL_comm (pq k) (X (Sum.inr 1))
  simp only [X1, mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [show ∀ A B C D E F : End₂, A - (b • C + D) - (B - (b • E + F)) = (A - B) - b • (C - E) - (D - F)
    by intros; module, h1, h2, h3, smul_zero]
  abel

theorem pq_Xm1 (a b : ℚ) (k : ℕ) :
    mulL (pq k) * Xm1 a b - Xm1 a b * mulL (pq k) = -mulL (upL (pq k)) + mulL (L1R b (pq k)) := by
  have h1 := mulL_der upL (pq k)
  have h2 := mulL_der (L1R b) (pq k)
  have h3 := mulL_comm (pq k) (X (Sum.inl 1))
  simp only [Xm1, mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [show ∀ A B C D E F : End₂, a • A + C - D - (a • B + E - F) = a • (A - B) + (C - E) - (D - F)
    by intros; module, h1, h2, h3, smul_zero]
  abel

theorem pq_X0 (k : ℕ) : mulL (pq k) * X0 - X0 * mulL (pq k) = 0 := by
  have h1 := mulL_der degL (pq k)
  have h2 := mulL_der degR (pq k)
  simp only [X0, mul_sub, sub_mul]
  rw [show ∀ A B C D : End₂, A - B - (C - D) = (A - C) - (B - D) by intros; abel, h1, h2]
  have e1 : degL (pq k) = (k : ℚ) • pq k := by
    simp only [pq, degL, Derivation.leibniz, mkDerivation_X, Sum.elim_inl, Sum.elim_inr,
      smul_eq_mul, mul_smul_comm]
    simp [mul_comm]
  have e2 : degR (pq k) = (k : ℚ) • pq k := by
    simp only [pq, degR, Derivation.leibniz, mkDerivation_X, Sum.elim_inl, Sum.elim_inr,
      smul_eq_mul, mul_smul_comm]
    simp [mul_comm]
  rw [e1, e2]; abel

theorem CK_succ (K : ℕ) (hK : 1 ≤ K) : CK (K + 1) = CK K + ((K : ℚ)⁻¹) • mulL (pq K) := by
  rw [CK, CK, Finset.sum_Ico_succ_top hK]

/-- **`[C_K, X_1] = −a p̃_1 + p_{K−1} p̃_K`** (`K ≥ 2`; the last term is the truncation boundary). -/
theorem CK_X1 (a b : ℚ) (K : ℕ) :
    CK K * X1 a b - X1 a b * CK K =
      if 2 ≤ K then (-a) • mulL (X (Sum.inr 1)) + mulL (X (Sum.inl (K - 1)) * X (Sum.inr K)) else 0 := by
  induction K with
  | zero => simp [CK]
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [CK]
    rw [CK_succ K hK, add_mul, mul_add, show ∀ A B C D : End₂, A + B - (C + D) = (A - C) + (B - D) by
      intros; abel, ih, smul_mul_assoc, mul_smul_comm, smul_sub', pq_X1, L1L_pq, upR_pq]
    rcases Nat.lt_or_ge K 2 with h2 | h2
    · obtain rfl : K = 1 := by omega
      simp [pcL, mulL_C]
      module
    · have hK1 : K - 1 ≠ 0 := by omega
      simp only [ite_eq_left h2, ite_eq_left (by omega : 2 ≤ K + 1), pcL, hK1, ite_false, Nat.add_sub_cancel,
        mul_smul_comm, mulL_smul]
      rw [show X (Sum.inr K) * X (Sum.inl (K - 1)) = X (Sum.inl (K - 1)) * X (Sum.inr K) by ring]
      rw [smul_add, smul_neg, smul_smul, smul_smul, inv_mul_cancel₀ (by positivity)]
      module

/-- **`[C_K, X_{−1}] = b p_1 − p_K p̃_{K−1}`** (`K ≥ 2`). -/
theorem CK_Xm1 (a b : ℚ) (K : ℕ) :
    CK K * Xm1 a b - Xm1 a b * CK K =
      if 2 ≤ K then b • mulL (X (Sum.inl 1)) - mulL (X (Sum.inl K) * X (Sum.inr (K - 1))) else 0 := by
  induction K with
  | zero => simp [CK]
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [CK]
    rw [CK_succ K hK, add_mul, mul_add, show ∀ A B C D : End₂, A + B - (C + D) = (A - C) + (B - D) by
      intros; abel, ih, smul_mul_assoc, mul_smul_comm, smul_sub', pq_Xm1, upL_pq, L1R_pq]
    rcases Nat.lt_or_ge K 2 with h2 | h2
    · obtain rfl : K = 1 := by omega
      simp [pcR, mulL_C]
      rw [mul_comm (X (Sum.inr 1))]
      abel
    · have hK1 : K - 1 ≠ 0 := by omega
      simp only [ite_eq_left h2, ite_eq_left (by omega : 2 ≤ K + 1), pcR, hK1, ite_false, Nat.add_sub_cancel,
        mul_smul_comm, mulL_smul]
      rw [show X (Sum.inr K) * X (Sum.inl (K + 1)) = X (Sum.inl (K + 1)) * X (Sum.inr K) by ring]
      rw [smul_add, smul_neg, smul_smul, smul_smul, inv_mul_cancel₀ (by positivity)]
      module

/-- **`[C_K, X_0] = 0`**. -/
theorem CK_X0 (K : ℕ) : CK K * X0 - X0 * CK K = 0 := by
  rw [CK, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_sub', pq_X0, smul_zero]

/-! ## The ω-twin: the dual Cauchy kernel -/

/-- `C^ω_K = Σ_{1≤k<K} (−1)^{k−1} p_k p̃_k / k`, the logarithm of the dual Cauchy kernel `Σ s_ν s̃_{ν'}`. -/
noncomputable def COmK (K : ℕ) : End₂ := ∑ k ∈ Ico 1 K, (sgn k * (k : ℚ)⁻¹) • mulL (pq k)

/-- **`ω ⊗ 1` sends `C_K` to `C^ω_K`**. -/
theorem omegaL_CK (K : ℕ) (F : Λ₂) : omegaL (CK K F) = COmK K (omegaL F) := by
  simp only [CK, COmK, LinearMap.sum_apply, LinearMap.smul_apply, mulL, LinearMap.mulLeft_apply,
    map_sum, map_smul, map_mul, pq, omegaL, aeval_X, Sum.elim_inl, Sum.elim_inr]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smul_mul_assoc, smul_smul]
  ring_nf

theorem deltaOmK_eq_Ico (K : ℕ) : deltaOmK K = ∑ k ∈ Ico 1 K, (sgn k * k) • (dL k * dR k) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [deltaOmK]
  · rw [deltaOmK, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hK]; simp

/-- **The fermionic twin has the same `H`**: `[δ^ω_K, C^ω_K] = H_K`. -/
theorem deltaOmK_COmK (K : ℕ) : deltaOmK K * COmK K - COmK K * deltaOmK K = HK K := by
  rw [deltaOmK_eq_Ico, COmK, comm_sum_sum]
  simp only [smul_comm_smul, T_pq, smul_ite, smul_zero, sum_Ico_ite]
  rw [Finset.sum_ite_of_true (fun k hk => hk)]
  rw [Finset.sum_congr rfl fun k hk => by
    rw [show sgn k * (k : ℚ) * (sgn k * (k : ℚ)⁻¹) = (sgn k * sgn k) * ((k : ℚ) * (k : ℚ)⁻¹) by ring,
      sgn_mul_self, mul_inv_cancel₀ (by have := (Finset.mem_Ico.mp hk).1; positivity), one_mul,
      one_smul]]
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, HK, ← Nat.cast_smul_eq_nsmul ℚ]

end RMT.Fock.WeilCauchy
