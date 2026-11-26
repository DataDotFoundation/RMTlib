import RMTlib.Fock.WeilCauchy

/-!
# Dehaye's `Δ` shifts charge (W3)

Companion to `bridge/links/virasoro-briefing.md` (§9); checks in `bridge/scripts/charge_kernel.py`. GRH-free.

`Δ = exp δ` commutes with the twisted-diagonal `sl_2` `X_n` only at charge 0
(`RMT.Fock.DehayeDelta.expDelta_X1`). At charges `(a, b)` it **intertwines charge sectors**:

  `Δ X_1(a, b) = X_1(a − b, b) Δ`,   `Δ X_{−1}(a, b) = X_{−1}(a, b − a) Δ`.

The reason: `[δ, X_1] = −b α_1` (`RMT.Fock.DehayeDelta.delta_X1`), `[δ, α_1] = 0` (`delta_dL_one`), and
`X_1(a, b) − b α_1 = X_1(a − b, b)` because `L_1` is affine in its charge (`X1_shift`). Here this is stated
for the truncations of `Δ` (`expDelta_X1_shift`, `expDelta_Xm1_shift`):

  `Δ_{M+1}(X_1 F) = X_1 Δ_{M+1} F − b ∂_{p_1} Δ_M F`,

which is `X_1(a − b, b) Δ F` once both truncations equal `Δ F`.

Computed only (`charge_kernel.py` B–D): no kernel `Σ w(ν) s_ν^⊥ ⊗ s̃_ν^⊥` with `w = 1`, `∏(N + c)` or
`1/∏(N + c)`, nor any coherent shift of `Δ`, commutes with `X_{±1}` at a nonzero charge, and the ∞-weighted
kernels intertwine no `X_{±1}` sectors at all. The ∞ weight breaks the twisted-diagonal `sl_2`.
-/

open MvPolynomial Finset
open RMT.Fock.DehayeDelta RMT.Fock.WeilCauchy

namespace RMT.Fock.ChargeKernel

/-! ## `L_1` is affine in its charge -/

theorem L1L_shift (a b : ℚ) : L1L a = L1L (a - b) + b • pderiv (Sum.inl 1) := by
  apply MvPolynomial.derivation_ext
  rintro (k | k)
  · rcases k with _ | _ | k
    · simp [L1L]
    · simp [L1L, pcL]
      rw [show (b • (1 : Λ₂)) = C b by simp [smul_eq_C_mul]]; ring
    · simp [L1L, pcL]
  · simp [L1L]

theorem L1R_shift (a b : ℚ) : L1R b = L1R (b - a) + a • pderiv (Sum.inr 1) := by
  apply MvPolynomial.derivation_ext
  rintro (k | k)
  · simp [L1R]
  · rcases k with _ | _ | k
    · simp [L1R]
    · simp [L1R, pcR]
      rw [show (a • (1 : Λ₂)) = C a by simp [smul_eq_C_mul]]; ring
    · simp [L1R, pcR]

/-- **`X_1(a, b) − b α_1 = X_1(a − b, b)`**. -/
theorem X1_shift (a b : ℚ) : X1 a b - b • dL 1 = X1 (a - b) b := by
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation ℚ Λ₂ Λ₂ => D F) (L1L_shift a b)
  simp only [add_apply, smul_apply] at h
  simp only [X1, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    dL, h]
  abel

/-- **`X_{−1}(a, b) + a α̃_1 = X_{−1}(a, b − a)`**. -/
theorem Xm1_shift (a b : ℚ) : Xm1 a b + a • dR 1 = Xm1 a (b - a) := by
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation ℚ Λ₂ Λ₂ => D F) (L1R_shift a b)
  simp only [add_apply, smul_apply] at h
  simp only [Xm1, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    dR, h]
  abel

/-! ## `δ` is linear and commutes with `∂_{p_1}`, `∂_{p̃_1}` -/

theorem delta_add (F G : Λ₂) : delta (F + G) = delta F + delta G := by
  set K := max (max (bound F) (bound G)) (bound (F + G))
  rw [delta_eq (K := K) (by omega), delta_eq (K := K) (by omega), delta_eq (F := G) (K := K) (by omega),
    map_add]

theorem delta_smul (c : ℚ) (F : Λ₂) : delta (c • F) = c • delta F := by
  set K := max (bound F) (bound (c • F))
  rw [delta_eq (K := K) (by omega), delta_eq (K := K) (by omega), map_smul]

theorem deltaK_dL (K j : ℕ) (F : Λ₂) : deltaK K (dL j F) = dL j (deltaK K F) := by
  simp only [deltaK, LinearMap.sum_apply, LinearMap.smul_apply, mul_apply_eq_comp, map_sum, map_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [dL, dR, Derivation.coeFn_coe]
  rw [pd_comm (Sum.inr k) (Sum.inl j), pd_comm (Sum.inl k) (Sum.inl j)]

theorem deltaK_dR (K j : ℕ) (F : Λ₂) : deltaK K (dR j F) = dR j (deltaK K F) := by
  simp only [deltaK, LinearMap.sum_apply, LinearMap.smul_apply, mul_apply_eq_comp, map_sum, map_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [dL, dR, Derivation.coeFn_coe]
  rw [pd_comm (Sum.inr k) (Sum.inr j), pd_comm (Sum.inl k) (Sum.inr j)]

/-- **`[δ, α_1] = 0`** (more generally `[δ, ∂_{p_j}] = 0`). -/
theorem delta_dL (j : ℕ) (F : Λ₂) : delta (dL j F) = dL j (delta F) := by
  set K := max (bound F) (bound (dL j F))
  rw [delta_eq (K := K) (by omega), delta_eq (K := K) (by omega), deltaK_dL]

/-- **`[δ, α̃_1] = 0`** (more generally `[δ, ∂_{p̃_j}] = 0`). -/
theorem delta_dR (j : ℕ) (F : Λ₂) : delta (dR j F) = dR j (delta F) := by
  set K := max (bound F) (bound (dR j F))
  rw [delta_eq (K := K) (by omega), delta_eq (K := K) (by omega), deltaK_dR]

/-! ## The truncated intertwining -/

/-- If `δ (T F) = T (δ F) + Y F` with `Y` commuting with `δ`, then
`δ^m (T F) = T (δ^m F) + m Y (δ^{m−1} F)`. -/
theorem iterate_comm (T Y : End₂) (hT : ∀ F, delta (T F) = T (delta F) + Y F)
    (hY : ∀ F, delta (Y F) = Y (delta F)) :
    ∀ (m : ℕ) (F : Λ₂), delta^[m + 1] (T F) = T (delta^[m + 1] F) + ((m + 1 : ℕ) : ℚ) • Y (delta^[m] F) := by
  have hYit : ∀ (m : ℕ) (G : Λ₂), delta^[m] (Y G) = Y (delta^[m] G) := by
    intro m; induction m with
    | zero => intro G; rfl
    | succ m ih => intro G; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hY]
  intro m
  induction m with
  | zero => intro F; simp [hT]
  | succ m ih =>
    intro F
    rw [Function.iterate_succ_apply', ih, delta_add, delta_smul, hT, hY,
      Function.iterate_succ_apply' delta (m + 1) F, Function.iterate_succ_apply' delta m F]
    push_cast
    module

theorem expDelta_comm_shift (T Y : End₂) (hT : ∀ F, delta (T F) = T (delta F) + Y F)
    (hY : ∀ F, delta (Y F) = Y (delta F)) (M : ℕ) (F : Λ₂) :
    expDelta (M + 1) (T F) = T (expDelta (M + 1) F) + Y (expDelta M F) := by
  simp only [expDelta, map_sum, map_smul]
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun m => ((m.factorial : ℚ)⁻¹) • T (delta^[m] F))]
  simp only [iterate_comm T Y hT hY, smul_add, Finset.sum_add_distrib, Function.iterate_zero_apply,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, smul_smul]
  have : ∀ m : ℕ, ((m + 1).factorial : ℚ)⁻¹ * ((m + 1 : ℕ) : ℚ) = (m.factorial : ℚ)⁻¹ := by
    intro m
    rw [Nat.factorial_succ]; push_cast
    rw [mul_inv, mul_comm ((m : ℚ) + 1)⁻¹, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  simp only [this]
  abel

/-- **`Δ` shifts the first copy's charge by `−b`**:
`Δ_{M+1}(X_1(a, b) F) = X_1(a, b) Δ_{M+1} F − b ∂_{p_1} Δ_M F`, i.e. `Δ X_1(a, b) = X_1(a − b, b) Δ` on any
polynomial once the truncations stabilise (`X1_shift`). -/
theorem expDelta_X1_shift (a b : ℚ) (M : ℕ) (F : Λ₂) :
    expDelta (M + 1) (X1 a b F) = X1 a b (expDelta (M + 1) F) + ((-b) • dL 1) (expDelta M F) := by
  refine expDelta_comm_shift _ _ (fun G => ?_) (fun G => ?_) M F
  · have := delta_X1 a b G
    rw [LinearMap.smul_apply]
    rw [sub_eq_iff_eq_add] at this
    rw [this, add_comm]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, delta_smul, delta_dL]

/-- **`Δ` shifts the second copy's charge by `−a`**:
`Δ_{M+1}(X_{−1}(a, b) F) = X_{−1}(a, b) Δ_{M+1} F + a ∂_{p̃_1} Δ_M F`, i.e. `Δ X_{−1}(a, b) = X_{−1}(a, b − a) Δ`
(`Xm1_shift`). -/
theorem expDelta_Xm1_shift (a b : ℚ) (M : ℕ) (F : Λ₂) :
    expDelta (M + 1) (Xm1 a b F) = Xm1 a b (expDelta (M + 1) F) + (a • dR 1) (expDelta M F) := by
  refine expDelta_comm_shift _ _ (fun G => ?_) (fun G => ?_) M F
  · have := delta_Xm1 a b G
    rw [LinearMap.smul_apply]
    rw [sub_eq_iff_eq_add] at this
    rw [this, add_comm]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, delta_smul, delta_dR]

end RMT.Fock.ChargeKernel
