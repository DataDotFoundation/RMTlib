import RMTlib.Fock.Virasoro

/-!
# `L_{±2}` and the central charge `c = 1` (W4)

Companion to `bridge/links/virasoro-briefing.md` (§10); checks in `bridge/scripts/virasoro_central.py`.
GRH-free.

The Sugawara modes `L_n = ½ Σ_k :α_{n−k} α_k:` at charge `a` (`α_0 = a`) on `Λ = ℚ[p_1, p_2, …]`
(`RMTlib.Fock.Virasoro`). For `n = ±2` they are finite on polynomials:

* `L_2 = ½ ∂_1² + 2a ∂_2 + Σ_{k≥1} (k+2) p_k ∂_{k+2}` (`L2`);
* `L_{−2} = ½ p_1² + a p_2 + Σ_{k≥1} k p_{k+2} ∂_k` (`Lm2`).

The central extension appears in `[L_2, L_{−2}] = 4 L_0 + ½` (`L2_Lm2`): `c/12 · (2³ − 2) = ½`, so **`c = 1`**,
at every charge. The `½` is the one place where normal ordering matters, `[½∂_1², ½p_1²]`. Also
`[L_0, L_{±2}] = ∓2 L_{±2}` (`L0_L2`, `L0_Lm2`). The ω-twin is `ω L_{±2}^{(a)} ω = L_{±2}^{(−a)}`
(`omega_L2`, `omega_Lm2`), and with `ω L_{±1}^{(a)} ω = −L_{±1}^{(−a)}` this is `ω L_n^{(a)} ω = (−1)^n L_n^{(−a)}`, an
automorphism of Virasoro that fixes `c`. So the fermionic (`Λ`-side, charge `−a`) picture has `c = 1` as well.

The whole algebra (`|m|, |n|, |m+n| ≤ 3`) is checked in the script; `[L_1, L_{−2}] = 3L_{−1}` etc. are not
stated here.
-/

open MvPolynomial

namespace RMT.Fock.Virasoro

/-- The derivation part of `L_2`: `2a ∂_2 + Σ_k (k+2) p_k ∂_{k+2}` (`p_j ↦ j p_{j−2}`, `p_0 = a`). -/
noncomputable def down2 (a : ℚ) : Der :=
  mkDerivation ℚ fun j => if j < 2 then 0 else (j : ℚ) • pc a (j - 2)

/-- The derivation part of `L_{−2}`: `Σ_k k p_{k+2} ∂_k`. -/
noncomputable def up2 : Der := mkDerivation ℚ fun k => (k : ℚ) • X (k + 2)

/-- `∂/∂p_1` as an endomorphism. -/
noncomputable def D1 : Module.End ℚ Λ := (pderiv 1 : Der)

/-- **`L_2` at charge `a`**: `½ ∂_1² + down₂`. -/
noncomputable def L2 (a : ℚ) : Module.End ℚ Λ := (1 / 2 : ℚ) • (D1 * D1) + (down2 a : Λ →ₗ[ℚ] Λ)

/-- **`L_{−2}` at charge `a`**: `½ p_1² + a p_2 + up₂`. -/
noncomputable def Lm2 (a : ℚ) : Module.End ℚ Λ :=
  (1 / 2 : ℚ) • LinearMap.mulLeft ℚ (X 1 * X 1) + a • LinearMap.mulLeft ℚ (X 2) + (up2 : Λ →ₗ[ℚ] Λ)

theorem down2_X (a : ℚ) (j : ℕ) : down2 a (X j) = if j < 2 then 0 else (j : ℚ) • pc a (j - 2) :=
  mkDerivation_X _ _ _

theorem up2_X (k : ℕ) : up2 (X k) = (k : ℚ) • X (k + 2) := mkDerivation_X _ _ _

@[simp] theorem der_ite (D : Der) (p : Prop) [Decidable p] : D (if p then (1 : Λ) else 0) = 0 := by
  split_ifs <;> simp

/-- `[∂_1, up₂] = 0`. -/
theorem pd1_up2 : ⁅(pderiv 1 : Der), up2⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  intro k
  rw [Derivation.commutator_apply, up2_X, pderiv_X, Derivation.map_smul, pderiv_X]
  simp only [Pi.single_apply]
  split_ifs <;> first | omega | simp

/-- **`[down₂, up₂] = 4 deg − p_1 ∂_1`**. -/
theorem down2_up2 (a : ℚ) : ⁅down2 a, up2⁆ = (4 : ℚ) • deg - (X 1 : Λ) • (pderiv 1 : Der) := by
  apply MvPolynomial.derivation_ext
  intro k
  rw [Derivation.commutator_apply]
  rcases k with _ | _ | _ | k
  · simp [up2_X, down2_X, deg_X]
  · simp [up2_X, down2_X, deg_X, pc, smul_eq_mul]
    module
  · simp [up2_X, down2_X, deg_X, pc, Derivation.map_smul, smul_smul, smul_eq_mul]
    norm_num
  · simp [up2_X, down2_X, deg_X, pc, Derivation.map_smul, smul_smul, smul_eq_mul]
    module

theorem down2_X_one (a : ℚ) : down2 a (X 1) = 0 := by simp [down2_X]

theorem down2_X_two (a : ℚ) : down2 a (X 2) = (2 : ℚ) • C a := by simp [down2_X, pc]

theorem num_mul (n : ℕ) (g : Λ) : (n : Λ) * g = (n : ℚ) • g := by
  rw [smul_eq_C_mul, map_natCast]

/-- **The central charge is `1`**: `[L_2, L_{−2}] = 4 L_0 + ½`. -/
theorem L2_Lm2 (a : ℚ) : L2 a * Lm2 a - Lm2 a * L2 a = (4 : ℚ) • L0 a + (1 / 2 : ℚ) • 1 := by
  refine LinearMap.ext fun f => ?_
  have hF := congrArg (fun D : Der => D f) (down2_up2 a)
  simp only [Derivation.commutator_apply, Derivation.sub_apply, Derivation.smul_apply,
    smul_eq_mul] at hF
  have hC' : pderiv 1 (pderiv 1 (up2 f)) = up2 (pderiv 1 (pderiv 1 f)) := by
    have h1 := congrArg (fun D : Der => D f) pd1_up2
    have h2 := congrArg (fun D : Der => D (pderiv 1 f)) pd1_up2
    simp only [Derivation.commutator_apply, Derivation.zero_apply] at h1 h2
    rw [sub_eq_zero.mp h1, sub_eq_zero.mp h2]
  have hA : pderiv 1 (pderiv 1 (X 1 * X 1 * f)) =
      X 1 * X 1 * pderiv 1 (pderiv 1 f) + (4 : ℚ) • (X 1 * pderiv 1 f) + (2 : ℚ) • f := by
    have : pderiv 1 (pderiv 1 (X 1 * X 1 * f)) =
        X 1 * X 1 * pderiv 1 (pderiv 1 f) + ((4 : ℕ) : Λ) * (X 1 * pderiv 1 f) + ((2 : ℕ) : Λ) * f := by
      simp only [Derivation.leibniz, pderiv_X_self, smul_eq_mul, map_add, Derivation.map_one_eq_zero]
      push_cast; ring
    rw [this, num_mul, num_mul]; norm_num
  have hB : pderiv 1 (pderiv 1 (X 2 * f)) = X 2 * pderiv 1 (pderiv 1 f) := by
    simp [Derivation.leibniz, pderiv_X]
  have hD : down2 a (X 1 * X 1 * f) = X 1 * X 1 * down2 a f := by
    simp [Derivation.leibniz, down2_X_one]
  have hE : down2 a (X 2 * f) = X 2 * down2 a f + (2 * a) • f := by
    rw [Derivation.leibniz, down2_X_two, smul_eq_mul, smul_eq_mul, add_comm]
    rw [show f * ((2 : ℚ) • C a) = (2 * a) • f by
      rw [mul_smul_comm, mul_comm, ← smul_eq_C_mul, smul_smul, mul_comm]]
    rw [add_comm]
  simp only [L2, Lm2, L0, D1, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_add, map_smul,
    Module.End.one_apply, hA, hB, hC', hD, hE]
  linear_combination (norm := module) hF

/-! ## `L_0` grades `L_{±2}` -/

theorem deg_pd1 : ⁅deg, (pderiv 1 : Der)⁆ = -(pderiv 1 : Der) := by
  apply MvPolynomial.derivation_ext
  intro k
  rw [Derivation.commutator_apply, deg_X, pderiv_X, Derivation.map_smul, pderiv_X]
  simp only [Pi.single_apply, Derivation.neg_apply]
  split_ifs with h <;> simp [h]

theorem deg_down2 (a : ℚ) : ⁅deg, down2 a⁆ = (-2 : ℚ) • down2 a := by
  apply MvPolynomial.derivation_ext
  intro k
  rw [Derivation.commutator_apply]
  rcases k with _ | _ | _ | k
  · simp [down2_X, deg_X]
  · simp [down2_X, deg_X]
  · simp [down2_X, deg_X, pc, Derivation.map_smul, smul_smul]
  · simp [down2_X, deg_X, pc, Derivation.map_smul, smul_smul]
    module

theorem deg_up2 : ⁅deg, up2⁆ = (2 : ℚ) • up2 := by
  apply MvPolynomial.derivation_ext
  intro k
  rw [Derivation.commutator_apply, up2_X, deg_X, Derivation.map_smul, Derivation.map_smul, deg_X,
    up2_X]
  simp only [Derivation.smul_apply, up2_X, smul_smul]
  push_cast; module

/-- **`[L_0, L_2] = −2 L_2`**. -/
theorem L0_L2 (a : ℚ) : L0 a * L2 a - L2 a * L0 a = (-2 : ℚ) • L2 a := by
  refine LinearMap.ext fun f => ?_
  have h1 : ∀ g, deg (pderiv 1 g) = pderiv 1 (deg g) - pderiv 1 g := fun g => by
    have := congrArg (fun D : Der => D g) deg_pd1
    simp only [Derivation.commutator_apply, Derivation.neg_apply] at this
    rw [sub_eq_iff_eq_add] at this; rw [this]; abel
  have h2 := congrArg (fun D : Der => D f) (deg_down2 a)
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at h2
  simp only [L0, L2, D1, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply, Derivation.coeFn_coe, map_add, map_smul, h1, map_sub]
  linear_combination (norm := module) h2

/-- **`[L_0, L_{−2}] = 2 L_{−2}`**. -/
theorem L0_Lm2 (a : ℚ) : L0 a * Lm2 a - Lm2 a * L0 a = (2 : ℚ) • Lm2 a := by
  refine LinearMap.ext fun f => ?_
  have h2 := congrArg (fun D : Der => D f) deg_up2
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at h2
  have e1 : deg (X 1 * X 1 * f) = X 1 * X 1 * deg f + (2 : ℚ) • (X 1 * X 1 * f) := by
    simp only [Derivation.leibniz, deg_X, smul_eq_mul, smul_eq_C_mul, Nat.cast_one, C_1]
    rw [show (C (2 : ℚ) : Λ) = 2 from map_ofNat C 2]
    ring
  have e2 : deg (X 2 * f) = X 2 * deg f + (2 : ℚ) • (X 2 * f) := by
    simp only [Derivation.leibniz, deg_X, smul_eq_mul, smul_eq_C_mul, Nat.cast_ofNat]
    rw [show (C (2 : ℚ) : Λ) = 2 from map_ofNat C 2]
    ring
  simp only [L0, Lm2, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, LinearMap.mulLeft_apply, Module.End.one_apply, Derivation.coeFn_coe, map_add,
    map_smul, e1, e2]
  linear_combination (norm := module) h2

/-! ## The ω-twin: `ω L_{±2}^{(a)} ω = L_{±2}^{(−a)}` -/

theorem omega_pd1 (f : Λ) : omega (pderiv 1 f) = pderiv 1 (omega f) := by
  refine intertwine omega _ _ (fun k => ?_) f
  rw [pderiv_X, omega_X, Derivation.map_smul, pderiv_X]
  simp only [Pi.single_apply]
  split_ifs with h
  · subst h; simp
  · simp

theorem omega_down2 (a : ℚ) (f : Λ) : omega (down2 a f) = down2 (-a) (omega f) := by
  refine intertwine omega _ _ (fun k => ?_) f
  rcases k with _ | _ | _ | k
  · simp [down2_X, omega_X]
  · simp [down2_X, omega_X]
  · simp [down2_X, omega_X, pc, Derivation.map_smul, algHom_C]; norm_num
  · simp [down2_X, omega_X, pc, Derivation.map_smul, smul_smul, pow_succ]; ring

theorem omega_up2 (f : Λ) : omega (up2 f) = up2 (omega f) := by
  refine intertwine omega _ _ (fun k => ?_) f
  simp [up2_X, omega_X, Derivation.map_smul, smul_smul, pow_succ]; ring

/-- **`ω L_2^{(a)} = L_2^{(−a)} ω`**. -/
theorem omega_L2 (a : ℚ) (f : Λ) : omega (L2 a f) = L2 (-a) (omega f) := by
  simp only [L2, D1, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Derivation.coeFn_coe, map_add, map_smul, omega_pd1, omega_down2]

/-- **`ω L_{−2}^{(a)} = L_{−2}^{(−a)} ω`**. -/
theorem omega_Lm2 (a : ℚ) (f : Λ) : omega (Lm2 a f) = Lm2 (-a) (omega f) := by
  simp only [Lm2, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, map_smul, map_mul, omega_X, omega_up2]
  norm_num

end RMT.Fock.Virasoro

/-! ## The `N`-row window: `L_{−2}` descends to `N` variables, `L_2` does not (RMTlib#99) -/

namespace RMT.Fock.Virasoro

open MvPolynomial

variable (N : ℕ)

/-- `Σ_i x_i³ ∂/∂x_i` is `up₂` in `N` variables: `(Σ_i x_i³ ∂_{x_i}) ∘ ev = ev ∘ up₂`. -/
theorem ev_up2 (f : Λ) : ev N (up2 f) = xD N 3 (ev N f) := by
  refine intertwine (ev N) _ _ (fun k => ?_) f
  rcases k with _ | k
  · simp [up2_X, ev]
  · simp only [up2_X, ev, aeval_X, map_smul]
    rw [xD_psum N 3 k]

/-- **`L_{−2}` at charge `N` descends to `N` variables** (RMTlib#99 item 1, the `−2` twin of `ev_L1`):
`ev (L_{−2}^{(N)} f) = Σ_i x_i³ ∂_i (ev f) + (N p_2 + ½ p_1²) · ev f`. -/
theorem ev_Lm2 (f : Λ) :
    ev N (Lm2 N f) = xD N 3 (ev N f) +
      ((N : MvPolynomial (Fin N) ℚ) * psum (Fin N) ℚ 2 +
        (1 / 2 : ℚ) • (psum (Fin N) ℚ 1 * psum (Fin N) ℚ 1)) * ev N f := by
  simp only [Lm2, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_add,
    map_smul, map_mul, Derivation.coeFn_coe, ev_up2]
  simp only [ev, aeval_X]
  rw [smul_eq_C_mul, smul_eq_C_mul]
  simp only [smul_eq_C_mul, map_natCast, add_mul, mul_assoc]
  ring

/-- So **`ker (ev N)` is `L_{−2}^{(N)}`-stable**: shapes with more than `N` rows stay out of the
window under `L_{−2}`. -/
theorem ev_Lm2_eq_zero {f : Λ} (hf : ev N f = 0) : ev N (Lm2 N f) = 0 := by
  rw [ev_Lm2, hf, map_zero, mul_zero, add_zero]

/-- `p_1² − p_2` (`= 2 s_{11}`) vanishes in one variable. -/
theorem ev_one_s11 : ev 1 ((X 1 : Λ) ^ 2 - X 2) = 0 := by
  simp [ev, psum, pow_two]

/-- **`L_2` does not descend** (RMTlib#99 item 2): `L_2^{(1)} (p_1² − p_2) = −1`, so it leaks out of
the one-row window although `p_1² − p_2` is in `ker (ev 1)`. The `N`-row window at `∞` is an `sl₂`
statement (`L_{±1}`, `L_{−2}`), not a Virasoro one. -/
theorem L2_one_s11 : L2 1 ((X 1 : Λ) ^ 2 - X 2) = -1 := by
  simp only [L2, D1, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sub]
  simp [pow_two, Derivation.leibniz, down2_X, pc, pderiv_X]
  module

theorem ev_one_L2_s11 : ev 1 (L2 1 ((X 1 : Λ) ^ 2 - X 2)) ≠ 0 := by
  rw [L2_one_s11, map_neg, map_one]
  exact neg_ne_zero.mpr one_ne_zero

end RMT.Fock.Virasoro
