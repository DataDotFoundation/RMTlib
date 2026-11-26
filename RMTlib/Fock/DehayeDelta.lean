import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Dehaye's contraction `Δ` and the twisted-diagonal `sl_2`

Companion to `bridge/links/virasoro-briefing.md`; checks in `bridge/scripts/dehaye_delta.py`.
GRH-free.

Two copies of the power-sum model of `RMTlib.Fock.Virasoro`: `Λ ⊗ Λ̃ = ℚ[p_1, p_2, …; p̃_1, p̃_2, …]`,
here `MvPolynomial (ℕ ⊕ ℕ) ℚ` with `X (inl k) = p_k` and `X (inr k) = p̃_k`. Dehaye's contraction
(*On an identity due to ((Bump and Diaconis) and (Tracy and Widom))*, Canad. Math. Bull. 54 (2011))
is `Δ = exp δ`, with

  `δ = Σ_k k ∂_{p_k} ∂_{p̃_k} = Σ_k p_k^⊥ p̃_k^⊥ / k`,

the adjoint of multiplication by the Cauchy kernel `Σ_ν s_ν s̃_ν = exp(Σ_k p_k p̃_k / k)`. Dehaye's
identity `Δ(s_λ s̃_μ) = Σ_ν s_{λ/ν} s̃_{μ/ν}` (the Jacobi–Trudi identity "differentiated by `Δ`", behind the
Bump–Diaconis / Tracy–Widom Toeplitz minors) is computed in the script, not proved here.

The sum over `k` is infinite but finite on each polynomial. So `δ` is defined through its truncations
`deltaK K = Σ_{k < K} k ∂_{p_k} ∂_{p̃_k}`, which stabilise once `K` exceeds every index occurring in the
polynomial (`delta_eq`).

## Main results

* `delta_mul_left`, `delta_mul_right`: `[δ, p_j] = α̃_j = j ∂_{p̃_j}` and `[δ, p̃_j] = α_j`. `δ` turns a
  creation operator on one copy into an annihilation operator on the other.
* `delta_X1`, `delta_Xm1`, `delta_X0`: with Virasoro's `L_n` at charge `a` on the first copy and at
  charge `b` on the second, and `X_n = L_n ⊗ 1 − 1 ⊗ L̃_{−n}` (the Chevalley involution on the second
  copy),
  `[δ, X_1] = −b α_1`, `[δ, X_{−1}] = a α̃_1`, `[δ, X_0] = 0` (with `X_0 = deg − d̃eg`).
  So `δ` commutes with the twisted-diagonal `sl_2` **exactly at charge 0**. The Cauchy kernel is the
  invariant pairing of the charge-0 module with its contragredient; at `∞` (charge `N`) the defect is
  `−N α_1`, which is why the Fock pairing at `∞` is the Hall pairing twisted by `∏ (N + c)`
  (`RMT.Fock.fischer_trX_pow_eq_twisted_hall`).
* `expDelta_X1`, `expDelta_Xm1`, `expDelta_X0`: hence every truncation `Σ_{m<M} δ^m/m!` of `Δ = exp δ`
  commutes with `X_{±1}, X_0` at charge 0 (`expDelta_comm`). Local nilpotency of `δ` (so that a
  truncation is `Δ` itself on a given polynomial) is not proved here.
* `omega2_delta`: `ω ⊗ ω` fixes `δ`. `omegaL_delta`: `ω ⊗ 1` turns `δ` into `δ^ω = Σ (−1)^{k−1} k ∂_{p_k} ∂_{p̃_k}`
  (`deltaOmK`), the contraction of the dual Cauchy kernel `Σ s_ν s̃_{ν'}`: the fermionic twin of `Δ`.

Not proved here: Dehaye's identity itself (needs Schur functions in power sums), and the charged
version of `Δ` that would commute with the `sl_2` at charge `N` (the Fock/Fischer kernel).
-/

open MvPolynomial

namespace RMT.Fock.DehayeDelta

/-- Two copies of the power-sum model: `X (inl k) = p_k`, `X (inr k) = p̃_k`. -/
abbrev Λ₂ := MvPolynomial (ℕ ⊕ ℕ) ℚ

/-- Linear endomorphisms of `Λ₂`. -/
abbrev End₂ := Module.End ℚ Λ₂

/-- `∂/∂p_k`. -/
noncomputable def dL (k : ℕ) : End₂ := (pderiv (Sum.inl k) : Derivation ℚ Λ₂ Λ₂)

/-- `∂/∂p̃_k`. -/
noncomputable def dR (k : ℕ) : End₂ := (pderiv (Sum.inr k) : Derivation ℚ Λ₂ Λ₂)

/-- The truncation `Σ_{k < K} k ∂_{p_k} ∂_{p̃_k}` of `δ`. -/
noncomputable def deltaK (K : ℕ) : End₂ := ∑ k ∈ Finset.range K, (k : ℚ) • (dL k * dR k)

/-- The index of a variable. -/
def idx : ℕ ⊕ ℕ → ℕ := Sum.elim id id

/-- One more than the largest index of a variable of `F`. -/
noncomputable def bound (F : Λ₂) : ℕ := F.vars.sup idx + 1

theorem dR_of_bound_le {F : Λ₂} {k : ℕ} (h : bound F ≤ k) : dR k F = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hk
  have := Finset.le_sup (f := idx) hk
  simp only [idx, Sum.elim_inr, id] at this
  simp only [bound, idx] at h
  omega

theorem deltaK_succ (K : ℕ) : deltaK (K + 1) = deltaK K + (K : ℚ) • (dL K * dR K) :=
  Finset.sum_range_succ _ _

theorem deltaK_stable {F : Λ₂} {K : ℕ} (h : bound F ≤ K) : deltaK K F = deltaK (bound F) F := by
  induction K, h using Nat.le_induction with
  | base => rfl
  | succ K hK ih =>
    rw [deltaK_succ, LinearMap.add_apply, ih, LinearMap.smul_apply, Module.End.mul_apply,
      dR_of_bound_le hK, map_zero, smul_zero, add_zero]

/-- Dehaye's `δ = Σ_k k ∂_{p_k} ∂_{p̃_k}`: the truncation at any `K ≥ bound F` (`delta_eq`). -/
noncomputable def delta (F : Λ₂) : Λ₂ := deltaK (bound F) F

theorem delta_eq {F : Λ₂} {K : ℕ} (h : bound F ≤ K) : delta F = deltaK K F :=
  (deltaK_stable h).symm

/-! ## `δ` against multiplication: `[δ, p_j] = α̃_j` -/

theorem dL_mul_left (k j : ℕ) (G : Λ₂) :
    dL k (X (Sum.inl j) * G) = X (Sum.inl j) * dL k G + if k = j then G else 0 := by
  rcases eq_or_ne k j with rfl | h
  · simp [dL, Derivation.leibniz, add_comm]
  · simp [dL, Derivation.leibniz, pderiv_X, h, Ne.symm h]

theorem dR_mul_left (k j : ℕ) (G : Λ₂) : dR k (X (Sum.inl j) * G) = X (Sum.inl j) * dR k G := by
  simp [dR, Derivation.leibniz, pderiv_X]

theorem dR_mul_right (k j : ℕ) (G : Λ₂) :
    dR k (X (Sum.inr j) * G) = X (Sum.inr j) * dR k G + if k = j then G else 0 := by
  rcases eq_or_ne k j with rfl | h
  · simp [dR, Derivation.leibniz, add_comm]
  · simp [dR, Derivation.leibniz, pderiv_X, h, Ne.symm h]

theorem dL_mul_right (k j : ℕ) (G : Λ₂) : dL k (X (Sum.inr j) * G) = X (Sum.inr j) * dL k G := by
  simp [dL, Derivation.leibniz, pderiv_X]

theorem dL_dR_comm (k l : ℕ) (G : Λ₂) : dL k (dR l G) = dR l (dL k G) := by
  have h : ⁅(pderiv (Sum.inl k) : Derivation ℚ Λ₂ Λ₂), pderiv (Sum.inr l)⁆ = 0 :=
    MvPolynomial.derivation_ext fun v => by
      rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
      simp only [Pi.single_apply]; split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℚ Λ₂ Λ₂ => D G) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] at h2
  exact h2

theorem term_mul_left (k j : ℕ) (G : Λ₂) :
    dL k (dR k (X (Sum.inl j) * G)) = X (Sum.inl j) * dL k (dR k G) + if k = j then dR k G else 0 := by
  rw [dR_mul_left, dL_mul_left]

theorem term_mul_right (k j : ℕ) (G : Λ₂) :
    dL k (dR k (X (Sum.inr j) * G)) = X (Sum.inr j) * dL k (dR k G) + if k = j then dL k G else 0 := by
  rw [dR_mul_right, map_add, dL_mul_right]
  split_ifs <;> simp

theorem deltaK_mul_aux (K : ℕ) (v : ℕ ⊕ ℕ) (D : ℕ → End₂)
    (hterm : ∀ k G, dL k (dR k (X v * G)) = X v * dL k (dR k G) + if k = idx v then D k G else 0)
    (G : Λ₂) :
    deltaK K (X v * G) = X v * deltaK K G + if idx v < K then (idx v : ℚ) • D (idx v) G else 0 := by
  induction K with
  | zero => simp [deltaK]
  | succ K ih =>
    rw [deltaK_succ, LinearMap.add_apply, ih, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply, hterm, LinearMap.smul_apply, Module.End.mul_apply, mul_add, mul_smul_comm]
    rcases lt_trichotomy (idx v) K with h | h | h
    · simp only [ite_eq_left h, ite_eq_left (Nat.lt_succ_of_lt h), ite_eq_right (Nat.ne_of_gt h)]; module
    · subst h; simp only [lt_irrefl, ite_false, ite_true, Nat.lt_succ_self]; module
    · simp only [ite_eq_right (by omega : ¬ idx v < K), ite_eq_right (by omega : ¬ idx v < K + 1),
        ite_eq_right (Nat.ne_of_lt h)]; module

theorem deltaK_mul_left (K j : ℕ) (G : Λ₂) :
    deltaK K (X (Sum.inl j) * G) =
      X (Sum.inl j) * deltaK K G + if j < K then (j : ℚ) • dR j G else 0 :=
  deltaK_mul_aux K (Sum.inl j) dR (fun k G => term_mul_left k j G) G

theorem deltaK_mul_right (K j : ℕ) (G : Λ₂) :
    deltaK K (X (Sum.inr j) * G) =
      X (Sum.inr j) * deltaK K G + if j < K then (j : ℚ) • dL j G else 0 :=
  deltaK_mul_aux K (Sum.inr j) dL (fun k G => term_mul_right k j G) G

/-- **`[δ, p_j] = α̃_j`**: `δ(p_j F) = p_j δF + j ∂_{p̃_j} F`. -/
theorem delta_mul_left (j : ℕ) (F : Λ₂) :
    delta (X (Sum.inl j) * F) = X (Sum.inl j) * delta F + (j : ℚ) • dR j F := by
  set K := max (max (bound F) (bound (X (Sum.inl j) * F))) (j + 1)
  rw [delta_eq (K := K) (by omega), delta_eq (K := K) (by omega), deltaK_mul_left,
    ite_eq_left (by omega)]

/-- **`[δ, p̃_j] = α_j`**: `δ(p̃_j F) = p̃_j δF + j ∂_{p_j} F`. -/
theorem delta_mul_right (j : ℕ) (F : Λ₂) :
    delta (X (Sum.inr j) * F) = X (Sum.inr j) * delta F + (j : ℚ) • dL j F := by
  set K := max (max (bound F) (bound (X (Sum.inr j) * F))) (j + 1)
  rw [delta_eq (K := K) (by omega), delta_eq (K := K) (by omega), deltaK_mul_right,
    ite_eq_left (by omega)]

/-! ## The twisted-diagonal `sl_2`

Virasoro's `L_n` at charge `a` on the first copy and at charge `b` on the second (as in
`RMTlib.Fock.Virasoro`), combined through the Chevalley involution `L_n ↦ −L_{−n}` on the second copy:
`X_1 = L_1^{(a)} ⊗ 1 − 1 ⊗ L̃_{−1}^{(b)}`, `X_{−1} = L_{−1}^{(a)} ⊗ 1 − 1 ⊗ L̃_1^{(b)}`, `X_0 = deg − d̃eg`. -/

/-- `p_k` on the first copy, with `p_0 = a`. -/
noncomputable def pcL (a : ℚ) (k : ℕ) : Λ₂ := if k = 0 then C a else X (Sum.inl k)

/-- `p̃_k` on the second copy, with `p̃_0 = b`. -/
noncomputable def pcR (b : ℚ) (k : ℕ) : Λ₂ := if k = 0 then C b else X (Sum.inr k)

/-- `L_1^{(a)} ⊗ 1 = a ∂_{p_1} + Σ_{k≥2} k p_{k−1} ∂_{p_k}`. -/
noncomputable def L1L (a : ℚ) : Derivation ℚ Λ₂ Λ₂ :=
  mkDerivation ℚ (Sum.elim (fun k => if k = 0 then 0 else (k : ℚ) • pcL a (k - 1)) fun _ => 0)

/-- `1 ⊗ L̃_1^{(b)}`. -/
noncomputable def L1R (b : ℚ) : Derivation ℚ Λ₂ Λ₂ :=
  mkDerivation ℚ (Sum.elim (fun _ => 0) fun k => if k = 0 then 0 else (k : ℚ) • pcR b (k - 1))

/-- The derivation part of `L_{−1} ⊗ 1`: `Σ_k k p_{k+1} ∂_{p_k}`. -/
noncomputable def upL : Derivation ℚ Λ₂ Λ₂ :=
  mkDerivation ℚ (Sum.elim (fun k => (k : ℚ) • X (Sum.inl (k + 1))) fun _ => 0)

/-- The derivation part of `1 ⊗ L̃_{−1}`. -/
noncomputable def upR : Derivation ℚ Λ₂ Λ₂ :=
  mkDerivation ℚ (Sum.elim (fun _ => 0) fun k => (k : ℚ) • X (Sum.inr (k + 1)))

/-- The degree on the first copy. -/
noncomputable def degL : Derivation ℚ Λ₂ Λ₂ :=
  mkDerivation ℚ (Sum.elim (fun k => (k : ℚ) • X (Sum.inl k)) fun _ => 0)

/-- The degree on the second copy. -/
noncomputable def degR : Derivation ℚ Λ₂ Λ₂ :=
  mkDerivation ℚ (Sum.elim (fun _ => 0) fun k => (k : ℚ) • X (Sum.inr k))

/-- Multiplication by `g`. -/
noncomputable def mulL (g : Λ₂) : End₂ := LinearMap.mulLeft ℚ g

/-- `X_1 = L_1^{(a)} ⊗ 1 − 1 ⊗ L̃_{−1}^{(b)}`. -/
noncomputable def X1 (a b : ℚ) : End₂ :=
  (L1L a : End₂) - (b • mulL (X (Sum.inr 1)) + (upR : End₂))

/-- `X_{−1} = L_{−1}^{(a)} ⊗ 1 − 1 ⊗ L̃_1^{(b)}`. -/
noncomputable def Xm1 (a b : ℚ) : End₂ :=
  (a • mulL (X (Sum.inl 1)) + (upL : End₂)) - (L1R b : End₂)

/-- `X_0 = deg ⊗ 1 − 1 ⊗ d̃eg` (the charge constants `a²/2 − b²/2` are central and omitted). -/
noncomputable def X0 : End₂ := (degL : End₂) - (degR : End₂)

theorem der_comm (D E : Derivation ℚ Λ₂ Λ₂) :
    (D : End₂) * E - E * D = ((⁅D, E⁆ : Derivation ℚ Λ₂ Λ₂) : End₂) := by
  rw [Derivation.commutator_coe_linear_map, Ring.lie_def]

theorem der_comm_mul (D : Derivation ℚ Λ₂ Λ₂) (g : Λ₂) :
    (D : End₂) * mulL g - mulL g * D = mulL (D g) := by
  refine LinearMap.ext fun F => ?_
  simp only [mulL, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
  ring

@[simp] theorem der_ite_one (D : Derivation ℚ Λ₂ Λ₂) (p : Prop) [Decidable p] :
    D (if p then (1 : Λ₂) else 0) = 0 := by
  split_ifs <;> simp

theorem dL_eq (k : ℕ) : dL k = ((pderiv (Sum.inl k) : Derivation ℚ Λ₂ Λ₂) : End₂) := rfl
theorem dR_eq (k : ℕ) : dR k = ((pderiv (Sum.inr k) : Derivation ℚ Λ₂ Λ₂) : End₂) := rfl

/-- `[∂_{p_k}, L_1^{(a)}] = (k + 1) ∂_{p_{k+1}}` for `k ≥ 1`, and `0` for `k = 0`. -/
theorem dL_L1L (a : ℚ) (k : ℕ) :
    dL k * (L1L a : End₂) - (L1L a : End₂) * dL k =
      if k = 0 then 0 else ((k + 1 : ℕ) : ℚ) • dL (k + 1) := by
  rw [dL_eq, der_comm]
  have : ⁅(pderiv (Sum.inl k) : Derivation ℚ Λ₂ Λ₂), L1L a⁆ =
      if k = 0 then 0 else ((k + 1 : ℕ) : ℚ) • pderiv (Sum.inl (k + 1)) := by
    apply MvPolynomial.derivation_ext
    rintro (m | m) <;>
      simp only [Derivation.commutator_apply, L1L, mkDerivation_X, Sum.elim_inl, Sum.elim_inr,
        pderiv_X, Pi.single_apply]
    · by_cases hk : k = 0
      · subst hk
        rcases m with _ | _ | m <;> simp [pcL, Derivation.map_smul]
      · rcases m with _ | _ | m
        · simp [pcL, hk]
        · simp [pcL, hk]
        · by_cases h : m + 1 = k
          · subst h; simp [pcL, Derivation.map_smul]
          · simp [pcL, Derivation.map_smul, hk, h]
    · split_ifs <;> simp [pderiv_X]
  rw [this]
  split_ifs <;> rfl

/-- `[∂_{p̃_k}, L_1^{(a)} ⊗ 1] = 0`. -/
theorem dR_L1L (a : ℚ) (k : ℕ) : dR k * (L1L a : End₂) - (L1L a : End₂) * dR k = 0 := by
  rw [dR_eq, der_comm]
  have : ⁅(pderiv (Sum.inr k) : Derivation ℚ Λ₂ Λ₂), L1L a⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    rintro (m | m) <;>
      simp only [Derivation.commutator_apply, L1L, mkDerivation_X, Sum.elim_inl, Sum.elim_inr,
        pderiv_X, Pi.single_apply]
    · rcases m with _ | _ | m <;> simp [pcL, Derivation.map_smul]
    · simp
  rw [this]; rfl

/-- To compute `[∂_v, D]` it suffices to differentiate `D` on the generators. -/
theorem pderiv_comm_eq (v : ℕ ⊕ ℕ) (D E : Derivation ℚ Λ₂ Λ₂)
    (h : ∀ w, pderiv v (D (X w)) = E (X w)) :
    ((pderiv v : Derivation ℚ Λ₂ Λ₂) : End₂) * D - D * (pderiv v : Derivation ℚ Λ₂ Λ₂) = E := by
  rw [der_comm]
  congr 1
  apply MvPolynomial.derivation_ext
  intro w
  rw [Derivation.commutator_apply, h, pderiv_X, Pi.single_apply, der_ite_one, sub_zero]

theorem dL_upR (k : ℕ) : dL k * (upR : End₂) - (upR : End₂) * dL k = 0 := by
  have := pderiv_comm_eq (Sum.inl k) upR 0 (by rintro (m | m) <;> simp [upR, Derivation.map_smul])
  rw [dL_eq, this]; rfl

theorem dR_upR (k : ℕ) :
    dR k * (upR : End₂) - (upR : End₂) * dR k = ((k - 1 : ℕ) : ℚ) • dR (k - 1) := by
  have := pderiv_comm_eq (Sum.inr k) upR (((k - 1 : ℕ) : ℚ) • pderiv (Sum.inr (k - 1))) (by
    rintro (m | m)
    · simp [upR]
    · simp only [upR, mkDerivation_X, Sum.elim_inr, Derivation.map_smul, pderiv_X,
        Derivation.smul_apply, Pi.single_apply, Sum.inr.injEq]
      by_cases h : m + 1 = k
      · subst h; simp
      · rw [ite_eq_right h]
        by_cases h' : m = k - 1
        · have hk : k = 0 := by omega
          subst hk; simp
        · simp [h'])
  rw [dR_eq, this]; rfl

theorem dL_upL (k : ℕ) :
    dL k * (upL : End₂) - (upL : End₂) * dL k = ((k - 1 : ℕ) : ℚ) • dL (k - 1) := by
  have := pderiv_comm_eq (Sum.inl k) upL (((k - 1 : ℕ) : ℚ) • pderiv (Sum.inl (k - 1))) (by
    rintro (m | m)
    · simp only [upL, mkDerivation_X, Sum.elim_inl, Derivation.map_smul, pderiv_X,
        Derivation.smul_apply, Pi.single_apply, Sum.inl.injEq]
      by_cases h : m + 1 = k
      · subst h; simp
      · rw [ite_eq_right h]
        by_cases h' : m = k - 1
        · have hk : k = 0 := by omega
          subst hk; simp
        · simp [h']
    · simp [upL])
  rw [dL_eq, this]; rfl

theorem dR_upL (k : ℕ) : dR k * (upL : End₂) - (upL : End₂) * dR k = 0 := by
  have := pderiv_comm_eq (Sum.inr k) upL 0 (by rintro (m | m) <;> simp [upL, Derivation.map_smul])
  rw [dR_eq, this]; rfl

theorem dL_L1R (b : ℚ) (k : ℕ) : dL k * (L1R b : End₂) - (L1R b : End₂) * dL k = 0 := by
  have := pderiv_comm_eq (Sum.inl k) (L1R b) 0 (by
    rintro (m | m)
    · simp [L1R]
    · rcases m with _ | _ | m <;> simp [L1R, pcR, Derivation.map_smul])
  rw [dL_eq, this]; rfl

theorem dR_L1R (b : ℚ) (k : ℕ) :
    dR k * (L1R b : End₂) - (L1R b : End₂) * dR k =
      if k = 0 then 0 else ((k + 1 : ℕ) : ℚ) • dR (k + 1) := by
  have := pderiv_comm_eq (Sum.inr k) (L1R b)
    (if k = 0 then 0 else ((k + 1 : ℕ) : ℚ) • pderiv (Sum.inr (k + 1))) (by
    rintro (m | m)
    · split_ifs <;> simp [L1R, pderiv_X]
    · by_cases hk : k = 0
      · subst hk
        rcases m with _ | _ | m <;> simp [L1R, pcR, Derivation.map_smul]
      · rcases m with _ | _ | m
        · simp [L1R, pcR, hk]
        · simp [L1R, pcR, hk]
        · by_cases h : m + 1 = k
          · subst h; simp [L1R, pcR, Derivation.map_smul]
          · simp [L1R, pcR, Derivation.map_smul, hk, h])
  rw [dR_eq, this]
  split_ifs <;> rfl

theorem dL_degL (k : ℕ) : dL k * (degL : End₂) - (degL : End₂) * dL k = (k : ℚ) • dL k := by
  have := pderiv_comm_eq (Sum.inl k) degL ((k : ℚ) • pderiv (Sum.inl k)) (by
    rintro (m | m)
    · simp only [degL, mkDerivation_X, Sum.elim_inl, Derivation.map_smul, pderiv_X,
        Derivation.smul_apply, Pi.single_apply, Sum.inl.injEq]
      by_cases h : m = k
      · subst h; simp
      · simp [h]
    · simp [degL])
  rw [dL_eq, this]; rfl

theorem dR_degR (k : ℕ) : dR k * (degR : End₂) - (degR : End₂) * dR k = (k : ℚ) • dR k := by
  have := pderiv_comm_eq (Sum.inr k) degR ((k : ℚ) • pderiv (Sum.inr k)) (by
    rintro (m | m)
    · simp [degR]
    · simp only [degR, mkDerivation_X, Sum.elim_inr, Derivation.map_smul, pderiv_X,
        Derivation.smul_apply, Pi.single_apply, Sum.inr.injEq]
      by_cases h : m = k
      · subst h; simp
      · simp [h])
  rw [dR_eq, this]; rfl

theorem dL_degR (k : ℕ) : dL k * (degR : End₂) - (degR : End₂) * dL k = 0 := by
  have := pderiv_comm_eq (Sum.inl k) degR 0 (by rintro (m | m) <;> simp [degR, Derivation.map_smul])
  rw [dL_eq, this]; rfl

theorem dR_degL (k : ℕ) : dR k * (degL : End₂) - (degL : End₂) * dR k = 0 := by
  have := pderiv_comm_eq (Sum.inr k) degL 0 (by rintro (m | m) <;> simp [degL, Derivation.map_smul])
  rw [dR_eq, this]; rfl

theorem dL_mulL (k : ℕ) (g : Λ₂) : dL k * mulL g - mulL g * dL k = mulL (dL k g) :=
  der_comm_mul _ g

theorem dR_mulL (k : ℕ) (g : Λ₂) : dR k * mulL g - mulL g * dR k = mulL (dR k g) :=
  der_comm_mul _ g

theorem mulL_ite (p : Prop) [Decidable p] : mulL (if p then (1 : Λ₂) else 0) = if p then 1 else 0 := by
  split_ifs <;> exact LinearMap.ext fun F => by simp [mulL]

/-- `[∂_{p_k}, X_1] = (k + 1) ∂_{p_{k+1}}` (`k ≥ 1`). -/
theorem dL_X1 (a b : ℚ) (k : ℕ) :
    dL k * X1 a b - X1 a b * dL k = if k = 0 then 0 else ((k + 1 : ℕ) : ℚ) • dL (k + 1) := by
  have h1 := dL_L1L a k
  have h2 := dL_upR k
  have h3 := dL_mulL k (X (Sum.inr 1))
  have h4 : dL k (X (Sum.inr 1)) = 0 := by simp [dL]
  rw [h4] at h3
  have h5 : mulL 0 = 0 := by ext1; simp [mulL]
  rw [h5] at h3
  rw [← h1]
  simp only [X1, mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [sub_eq_zero.mp h2, sub_eq_zero.mp h3]
  abel

/-- `[∂_{p̃_k}, X_1] = −b [k = 1] − (k − 1) ∂_{p̃_{k−1}}`. -/
theorem dR_X1 (a b : ℚ) (k : ℕ) :
    dR k * X1 a b - X1 a b * dR k =
      -((if k = 1 then b else 0) • (1 : End₂)) - ((k - 1 : ℕ) : ℚ) • dR (k - 1) := by
  have h1 := dR_L1L a k
  have h2 := dR_upR k
  have h3 := dR_mulL k (X (Sum.inr 1))
  have h4 : dR k (X (Sum.inr 1)) = if k = 1 then 1 else 0 := by
    simp [dR, pderiv_X, Pi.single_apply, eq_comm]
  rw [h4, mulL_ite] at h3
  rw [← h2]
  simp only [X1, mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  have e3 : dR k * mulL (X (Sum.inr 1)) = mulL (X (Sum.inr 1)) * dR k + (if k = 1 then 1 else 0) :=
    by rw [← h3]; abel
  rw [sub_eq_zero.mp h1, e3]
  split_ifs <;> first | (simp; done) | (simp; abel)

theorem End₂_mul_neg (A B : End₂) : A * -B = -(A * B) := LinearMap.ext fun _ => by simp

theorem End₂_mul_smul (c : ℚ) (A B : End₂) : A * (c • B) = c • (A * B) :=
  LinearMap.ext fun _ => by simp

/-- **The telescoping identity**: `[δ_K, X_1] = −b ∂_{p_1} [K ≥ 2] + (K − 1) K ∂_{p_K} ∂_{p̃_{K−1}}`. -/
theorem deltaK_X1 (a b : ℚ) (K : ℕ) :
    deltaK K * X1 a b - X1 a b * deltaK K =
      (if 2 ≤ K then (-b) • dL 1 else 0) + (((K - 1) * K : ℕ) : ℚ) • (dL K * dR (K - 1)) := by
  induction K with
  | zero => simp [deltaK]
  | succ K ih =>
    have hT : ((K : ℚ) • (dL K * dR K)) * X1 a b - X1 a b * ((K : ℚ) • (dL K * dR K)) =
        (K : ℚ) • (dL K * (dR K * X1 a b - X1 a b * dR K) + (dL K * X1 a b - X1 a b * dL K) * dR K) := by
      have e : dL K * dR K * X1 a b - X1 a b * (dL K * dR K) =
          dL K * (dR K * X1 a b - X1 a b * dR K) + (dL K * X1 a b - X1 a b * dL K) * dR K := by
        simp only [mul_sub, sub_mul, mul_assoc]; abel
      rw [smul_mul_assoc, mul_smul_comm, ← e, smul_sub]
    rw [deltaK_succ, add_mul, mul_add, show ∀ A B C D : End₂, A + B - (C + D) = (A - C) + (B - D) by
      intros; abel, ih, hT, dR_X1, dL_X1]
    rcases K with _ | _ | K
    · simp
    · simp [smul_add, smul_smul]
      rw [End₂_mul_neg, End₂_mul_smul, mul_one]; module
    · simp [smul_add, smul_smul]
      rw [End₂_mul_neg, End₂_mul_smul]
      module

/-- **`[δ, X_1] = −b α_1`**: `δ (X_1 F) − X_1 (δ F) = −b ∂_{p_1} F`. At charge `b = 0` (second copy),
`δ` commutes with `X_1 = L_1 ⊗ 1 − 1 ⊗ L̃_{−1}`. -/
theorem delta_X1 (a b : ℚ) (F : Λ₂) : delta (X1 a b F) - X1 a b (delta F) = (-b) • dL 1 F := by
  set K := max (max (bound F + 1) (bound (X1 a b F))) 2
  rw [delta_eq (K := K) (by omega), delta_eq (K := K) (by omega)]
  have h := congrArg (fun T : End₂ => T F) (deltaK_X1 a b K)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply] at h
  rw [h, ite_eq_left (by omega), dR_of_bound_le (by omega), map_zero, smul_zero, add_zero]
  rfl

/-- `[∂_{p_k}, X_{−1}] = a [k = 1] + (k − 1) ∂_{p_{k−1}}`. -/
theorem dL_Xm1 (a b : ℚ) (k : ℕ) :
    dL k * Xm1 a b - Xm1 a b * dL k =
      (if k = 1 then a else 0) • (1 : End₂) + ((k - 1 : ℕ) : ℚ) • dL (k - 1) := by
  have h1 := dL_L1R b k
  have h2 := dL_upL k
  have h3 := dL_mulL k (X (Sum.inl 1))
  have h4 : dL k (X (Sum.inl 1)) = if k = 1 then 1 else 0 := by
    simp [dL, pderiv_X, Pi.single_apply, eq_comm]
  rw [h4, mulL_ite] at h3
  rw [← h2]
  simp only [Xm1, mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  have e3 : dL k * mulL (X (Sum.inl 1)) = mulL (X (Sum.inl 1)) * dL k + (if k = 1 then 1 else 0) :=
    by rw [← h3]; abel
  rw [sub_eq_zero.mp h1, e3]
  split_ifs <;> first | (simp; done) | (simp; abel)

/-- `[∂_{p̃_k}, X_{−1}] = −(k + 1) ∂_{p̃_{k+1}}` (`k ≥ 1`). -/
theorem dR_Xm1 (a b : ℚ) (k : ℕ) :
    dR k * Xm1 a b - Xm1 a b * dR k = -(if k = 0 then 0 else ((k + 1 : ℕ) : ℚ) • dR (k + 1)) := by
  have h1 := dR_L1R b k
  have h2 := dR_upL k
  have h3 := dR_mulL k (X (Sum.inl 1))
  have h4 : dR k (X (Sum.inl 1)) = 0 := by simp [dR]
  have h5 : mulL 0 = 0 := LinearMap.ext fun _ => by simp [mulL]
  rw [h4, h5] at h3
  rw [← h1]
  simp only [Xm1, mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [sub_eq_zero.mp h2, sub_eq_zero.mp h3]
  abel

/-- **The telescoping identity for `X_{−1}`**:
`[δ_K, X_{−1}] = a ∂_{p̃_1} [K ≥ 2] − (K − 1) K ∂_{p_{K−1}} ∂_{p̃_K}`. -/
theorem deltaK_Xm1 (a b : ℚ) (K : ℕ) :
    deltaK K * Xm1 a b - Xm1 a b * deltaK K =
      (if 2 ≤ K then a • dR 1 else 0) - (((K - 1) * K : ℕ) : ℚ) • (dL (K - 1) * dR K) := by
  induction K with
  | zero => simp [deltaK]
  | succ K ih =>
    have hT : ((K : ℚ) • (dL K * dR K)) * Xm1 a b - Xm1 a b * ((K : ℚ) • (dL K * dR K)) =
        (K : ℚ) • (dL K * (dR K * Xm1 a b - Xm1 a b * dR K) + (dL K * Xm1 a b - Xm1 a b * dL K) * dR K) := by
      have e : dL K * dR K * Xm1 a b - Xm1 a b * (dL K * dR K) =
          dL K * (dR K * Xm1 a b - Xm1 a b * dR K) + (dL K * Xm1 a b - Xm1 a b * dL K) * dR K := by
        simp only [mul_sub, sub_mul, mul_assoc]; abel
      rw [smul_mul_assoc, mul_smul_comm, ← e, smul_sub]
    rw [deltaK_succ, add_mul, mul_add, show ∀ A B C D : End₂, A + B - (C + D) = (A - C) + (B - D) by
      intros; abel, ih, hT, dR_Xm1, dL_Xm1]
    rcases K with _ | _ | K
    · simp
    · simp [smul_add, smul_smul]
      rw [End₂_mul_neg, End₂_mul_smul]
      module
    · simp [smul_add, smul_smul]
      rw [End₂_mul_neg, End₂_mul_smul]
      module

/-- **`[δ, X_{−1}] = a α̃_1`**: at charge `a = 0` (first copy), `δ` commutes with
`X_{−1} = L_{−1} ⊗ 1 − 1 ⊗ L̃_1`. -/
theorem delta_Xm1 (a b : ℚ) (F : Λ₂) : delta (Xm1 a b F) - Xm1 a b (delta F) = a • dR 1 F := by
  set K := max (max (bound F) (bound (Xm1 a b F))) 2
  rw [delta_eq (K := K) (by omega), delta_eq (K := K) (by omega)]
  have h := congrArg (fun T : End₂ => T F) (deltaK_Xm1 a b K)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, 
    LinearMap.smul_apply] at h
  rw [h, ite_eq_left (by omega), dR_of_bound_le (by omega), map_zero, smul_zero, sub_zero]
  rfl

theorem deltaK_X0 (K : ℕ) : deltaK K * X0 - X0 * deltaK K = 0 := by
  induction K with
  | zero => simp [deltaK]
  | succ K ih =>
    have e : dL K * dR K * X0 - X0 * (dL K * dR K) =
        dL K * (dR K * X0 - X0 * dR K) + (dL K * X0 - X0 * dL K) * dR K := by
      simp only [mul_sub, sub_mul, mul_assoc]; abel
    have hR : dR K * X0 - X0 * dR K = -((K : ℚ) • dR K) := by
      have := dR_degL K; have := dR_degR K
      simp only [X0, mul_sub, sub_mul]
      rw [← dR_degR K, sub_eq_zero.mp (dR_degL K)]; abel
    have hL : dL K * X0 - X0 * dL K = (K : ℚ) • dL K := by
      simp only [X0, mul_sub, sub_mul]
      rw [← dL_degL K, sub_eq_zero.mp (dL_degR K)]; abel
    rw [deltaK_succ, add_mul, mul_add, show ∀ A B C D : End₂, A + B - (C + D) = (A - C) + (B - D) by
      intros; abel, ih, zero_add, smul_mul_assoc, mul_smul_comm,
      show ∀ (c : ℚ) (A B : End₂), c • A - c • B = c • (A - B) from fun c A B => (smul_sub c A B).symm,
      e, hR, hL, End₂_mul_neg, End₂_mul_smul, smul_mul_assoc]
    simp

/-- **`[δ, X_0] = 0`**: `δ` preserves the difference of the two degrees, at every charge. -/
theorem delta_X0 (F : Λ₂) : delta (X0 F) = X0 (delta F) := by
  set K := max (bound F) (bound (X0 F))
  rw [delta_eq (K := K) (by omega), delta_eq (K := K) (by omega)]
  have h := congrArg (fun T : End₂ => T F) (deltaK_X0 K)
  simpa [sub_eq_zero] using h

/-! ## `Δ = exp δ` at charge `0`: every power of `δ` commutes with the twisted-diagonal `sl_2` -/

/-- At charges `(a, 0)`, `δ` commutes with `X_1`. -/
theorem delta_X1_zero (a : ℚ) (F : Λ₂) : delta (X1 a 0 F) = X1 a 0 (delta F) := by
  have := delta_X1 a 0 F
  rwa [neg_zero, zero_smul, sub_eq_zero] at this

/-- At charges `(0, b)`, `δ` commutes with `X_{−1}`. -/
theorem delta_Xm1_zero (b : ℚ) (F : Λ₂) : delta (Xm1 0 b F) = Xm1 0 b (delta F) := by
  have := delta_Xm1 0 b F
  rwa [zero_smul, sub_eq_zero] at this

/-- The truncated exponential `Σ_{m < M} δ^m / m!`. On a polynomial of degree `< M` (in each copy)
it is `Δ = exp δ`, since `δ` lowers both degrees. -/
noncomputable def expDelta (M : ℕ) (F : Λ₂) : Λ₂ :=
  ∑ m ∈ Finset.range M, ((m.factorial : ℚ)⁻¹) • delta^[m] F

/-- Commuting with `δ` passes to its truncated exponentials. -/
theorem expDelta_comm (T : End₂) (hT : ∀ F, delta (T F) = T (delta F)) (M : ℕ) (F : Λ₂) :
    expDelta M (T F) = T (expDelta M F) := by
  have hit : ∀ m G, delta^[m] (T G) = T (delta^[m] G) := by
    intro m
    induction m with
    | zero => intro G; rfl
    | succ m ih => intro G; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hT]
  simp only [expDelta, map_sum, map_smul, hit]

/-- **Dehaye's `Δ` commutes with the twisted-diagonal `sl_2` at charge 0**:
`Δ X_n = X_n Δ` for `n = 1, −1, 0`, with `X_n = L_n ⊗ 1 − 1 ⊗ L̃_{−n}` (truncations of every order). -/
theorem expDelta_X1 (M : ℕ) (F : Λ₂) : expDelta M (X1 0 0 F) = X1 0 0 (expDelta M F) :=
  expDelta_comm _ (delta_X1_zero 0) M F

theorem expDelta_Xm1 (M : ℕ) (F : Λ₂) : expDelta M (Xm1 0 0 F) = Xm1 0 0 (expDelta M F) :=
  expDelta_comm _ (delta_Xm1_zero 0) M F

theorem expDelta_X0 (M : ℕ) (F : Λ₂) : expDelta M (X0 F) = X0 (expDelta M F) :=
  expDelta_comm _ delta_X0 M F

/-! ## The `ω`-twins: `ω ⊗ ω` fixes `δ`, `ω ⊗ 1` turns it into the dual-Cauchy contraction -/

/-- The sign of `ω` on a power sum: `ω p_k = (−1)^{k−1} p_k`. -/
def sgn (k : ℕ) : ℚ := (-1) ^ (k + 1)

theorem sgn_mul_self (k : ℕ) : sgn k * sgn k = 1 := by
  simp [sgn, ← mul_pow]

/-- `ω ⊗ ω`. -/
noncomputable def omega2 : Λ₂ →ₐ[ℚ] Λ₂ := aeval fun v => sgn (idx v) • X v

/-- `ω ⊗ 1`. -/
noncomputable def omegaL : Λ₂ →ₐ[ℚ] Λ₂ := aeval (Sum.elim (fun k => sgn k • X (Sum.inl k)) fun k => X (Sum.inr k))

/-- The dual-Cauchy contraction `δ^ω = Σ_k (−1)^{k−1} k ∂_{p_k} ∂_{p̃_k}`, the adjoint of multiplication
by `Σ_ν s_ν s̃_{ν'} = exp(Σ_k (−1)^{k−1} p_k p̃_k / k)` (truncations). -/
noncomputable def deltaOmK (K : ℕ) : End₂ := ∑ k ∈ Finset.range K, (sgn k * k) • (dL k * dR k)

/-- An algebra map intertwines two derivations if it does so on the generators. -/
theorem intertwine₂ (φ : Λ₂ →ₐ[ℚ] Λ₂) (D D' : Derivation ℚ Λ₂ Λ₂)
    (h : ∀ w, φ (D (X w)) = D' (φ (X w))) (F : Λ₂) : φ (D F) = D' (φ F) := by
  induction F using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.derivation_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      Derivation.map_algebraMap, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p k hp =>
    rw [Derivation.leibniz, map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, h, hp, smul_eq_mul, smul_eq_mul]

theorem omega2_pderiv (v : ℕ ⊕ ℕ) (F : Λ₂) :
    omega2 (pderiv v F) = (sgn (idx v) • pderiv v : Derivation ℚ Λ₂ Λ₂) (omega2 F) := by
  refine intertwine₂ omega2 _ _ (fun w => ?_) F
  simp only [omega2, aeval_X, Derivation.smul_apply, Derivation.map_smul, pderiv_X, Pi.single_apply]
  split_ifs with h
  · subst h; simp [smul_smul, sgn_mul_self]
  · simp

theorem omegaL_pderiv (v : ℕ ⊕ ℕ) (F : Λ₂) :
    omegaL (pderiv v F) =
      (Sum.elim (fun k => sgn k) (fun _ => (1 : ℚ)) v • pderiv v : Derivation ℚ Λ₂ Λ₂) (omegaL F) := by
  refine intertwine₂ omegaL _ _ (fun w => ?_) F
  rcases v with k | k <;> rcases w with m | m <;>
    simp only [omegaL, aeval_X, Sum.elim_inl, Sum.elim_inr, Derivation.smul_apply,
      Derivation.map_smul, pderiv_X, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      ite_false, one_smul, map_zero, smul_zero] <;> (try split_ifs with h) <;>
      simp_all [smul_smul, sgn_mul_self]

theorem omega2_dLdR (k : ℕ) (F : Λ₂) : omega2 (dL k (dR k F)) = dL k (dR k (omega2 F)) := by
  simp only [dL, dR, Derivation.coeFn_coe, omega2_pderiv, Derivation.smul_apply, Derivation.map_smul,
    smul_smul, idx, Sum.elim_inl, Sum.elim_inr, id, sgn_mul_self, one_smul]

theorem omegaL_dLdR (k : ℕ) (F : Λ₂) : omegaL (dL k (dR k F)) = sgn k • dL k (dR k (omegaL F)) := by
  simp only [dL, dR, Derivation.coeFn_coe, omegaL_pderiv, Derivation.smul_apply, 
    Sum.elim_inl, Sum.elim_inr, one_smul]

theorem omega2_deltaK (K : ℕ) (F : Λ₂) : omega2 (deltaK K F) = deltaK K (omega2 F) := by
  simp only [deltaK, LinearMap.sum_apply, map_sum, LinearMap.smul_apply,
    Module.End.mul_apply, map_smul, omega2_dLdR]

theorem omegaL_deltaK (K : ℕ) (F : Λ₂) : omegaL (deltaK K F) = deltaOmK K (omegaL F) := by
  simp only [deltaK, deltaOmK, LinearMap.sum_apply, map_sum, LinearMap.smul_apply,
    Module.End.mul_apply, map_smul, omegaL_dLdR, smul_smul, mul_comm]

/-- **`ω ⊗ ω` fixes `δ`**: `(ω⊗ω) δ = δ (ω⊗ω)`. The Cauchy kernel `Σ s_ν s̃_ν` is `ω ⊗ ω`-invariant. -/
theorem omega2_delta (F : Λ₂) : omega2 (delta F) = delta (omega2 F) := by
  rw [delta_eq (K := max (bound F) (bound (omega2 F))) (by omega),
    delta_eq (F := omega2 F) (K := max (bound F) (bound (omega2 F))) (by omega), omega2_deltaK]

/-- **The fermionic twin of `δ`**: `(ω ⊗ 1) δ_K = δ^ω_K (ω ⊗ 1)`, with `δ^ω` the contraction of the
dual Cauchy kernel `Σ s_ν s̃_{ν'}` (`Δ^ω(s_λ s̃_μ) = Σ_ν s_{λ/ν} s̃_{μ/ν'}`, computed). -/
theorem omegaL_delta (F : Λ₂) : omegaL (delta F) = deltaOmK (bound F) (omegaL F) := by
  rw [delta, omegaL_deltaK]

end RMT.Fock.DehayeDelta
