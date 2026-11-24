import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Virasoro's `sl_2` in the power-sum model, and the places as charge sectors

Companion to `bridge/links/virasoro-briefing.md`; checks in `bridge/scripts/virasoro_power_sum.py`.
GRH-free.

The bosonic Fock space is `Λ = ℚ[p_1, p_2, …]`, here `MvPolynomial ℕ ℚ` with `X k = p_k` (the
variable `X 0` is inert). The Heisenberg modes are `α_n = n ∂/∂p_n` for `n > 0` (`alpha`) and
multiplication by `p_n` for `n < 0`; `α_0` is a scalar, the **charge** `a`. In this model the
`sl_2` part of Virasoro at charge `a` is

* `L_1^{(a)} = a ∂_{p_1} + Σ_{k ≥ 2} k p_{k−1} ∂_{p_k}` (`L1`), a derivation;
* `L_0^{(a)} = a²/2 + Σ_k k p_k ∂_{p_k}` (`L0`, with the degree derivation `deg`);
* `L_{−1}^{(a)} = a p_1 + Σ_k k p_{k+1} ∂_{p_k}` (`Lm1`, with the derivation `up`).

On Schur functions, `∂_{p_1}` is Young's lattice's down operator `D_1` and `L_1^{(0)}` is the
content-weighted one, `D_c` (computed, `virasoro_power_sum.py` E together with D). So
`D_{a + c} = a D_1 + D_c` is `L_1^{(a)}` (`L1_eq`, the twin of `RMT.Symmetric.Corners.down_affine`).
The places are charge sectors: `∞` is `L_1^{(N)}`, the charged unramified datum of
`RMT.Places.LocalDatum.unramifiedCharged` is `T · L_1^{(k)}`, and the uncharged one is `T α_1`. More
uniformly, the place with content `α c + β` is the point `(α, β)` (`place`), the charge `β/α` living
in `P¹` (the uncharged `p` is the point at infinity `α = 0`).

## Main results

* `alpha_one_L1_zero`: `[α_1, L_1^{(0)}] = α_2`, i.e. `[D_1, D_c] = p₂^⊥` on all of `Λ`.
* `place_comm`: `[D_{(α,β)}, D_{(α',β')}] = (α' β − α β') α_2`; two places commute iff they are the
  same point of `P¹` (when `α_2 ≠ 0`). `L1_comm`: `[L_1^{(a)}, L_1^{(b)}] = (a − b) α_2`.
* `L1_Lm1`, `L0_L1`, `L0_Lm1`: the `sl_2` relations `[L_1, L_{−1}] = 2 L_0`, `[L_0, L_{±1}] = ∓L_{±1}`.
* `omega_L1`, `omega_alpha_two`, `omega_Lm1`, `omega_L0`: the `ω`-twin. `ω p_k = (−1)^{k−1} p_k`
  sends `L_1^{(a)}` to `−L_1^{(−a)}` and `L_0^{(a)}` to `L_0^{(−a)}`: charge reflection.
* `ev_L1`, `ev_deg`, `ev_up`: the realisation in `N` variables, `p_k ↦ Σ_i x_i^k` (`ev`). Then
  `Σ_i ∂_{x_i}` is `L_1^{(N)}`, `Σ_i x_i ∂_{x_i}` is `deg` and `Σ_i x_i² ∂_{x_i}` is
  `L_{−1}^{(N)} − N p_1`: the rank `N` is the charge.

Not proved here: the Schur-function side, `Σ_i ∂_{x_i} s_λ = Σ (N + c) s_{λ − □}` (computed E;
the `x`-variable twin of `RMT.Fock.trD_sX`), which would turn `L1_eq` into a statement about
`RMT.Symmetric.Corners.down`. No `L_{±2}`, hence no central charge.
-/

open MvPolynomial

namespace RMT.Fock.Virasoro

/-- The bosonic Fock space `ℚ[p_1, p_2, …]`; the variable `X k` is the power sum `p_k`. -/
abbrev Λ := MvPolynomial ℕ ℚ

/-- Derivations of `Λ`. -/
abbrev Der := Derivation ℚ Λ Λ

/-- The Heisenberg annihilation mode `α_n = n ∂/∂p_n`. -/
noncomputable def alpha (n : ℕ) : Der := (n : ℚ) • pderiv n

/-- `p_k`, with `p_0 = a` the charge. -/
noncomputable def pc (a : ℚ) (k : ℕ) : Λ := if k = 0 then C a else X k

/-- Virasoro's `L_1` at charge `a`: `a ∂_{p_1} + Σ_{k≥2} k p_{k−1} ∂_{p_k}`. -/
noncomputable def L1 (a : ℚ) : Der :=
  mkDerivation ℚ fun k => if k = 0 then 0 else (k : ℚ) • pc a (k - 1)

/-- The degree derivation `Σ_k k p_k ∂_{p_k}`. -/
noncomputable def deg : Der := mkDerivation ℚ fun k => (k : ℚ) • X k

/-- The derivation part of `L_{−1}`: `Σ_k k p_{k+1} ∂_{p_k}`. -/
noncomputable def up : Der := mkDerivation ℚ fun k => (k : ℚ) • X (k + 1)

/-- The down operator of the place with content `α c + β`: `α D_c + β D_1`. -/
noncomputable def place (α β : ℚ) : Der := α • L1 0 + β • alpha 1

theorem alpha_X (n k : ℕ) : alpha n (X k) = if k = n then (n : ℚ) • 1 else 0 := by
  classical
  simp only [alpha, Derivation.smul_apply, pderiv_X, Pi.single_apply]
  split_ifs <;> simp

theorem L1_X (a : ℚ) (k : ℕ) :
    L1 a (X k) = if k = 0 then 0 else (k : ℚ) • pc a (k - 1) := mkDerivation_X _ _ _

theorem deg_X (k : ℕ) : deg (X k) = (k : ℚ) • X k := mkDerivation_X _ _ _

theorem up_X (k : ℕ) : up (X k) = (k : ℚ) • X (k + 1) := mkDerivation_X _ _ _

/-- **`L_1` is affine in the charge**: `L_1^{(a)} = a α_1 + L_1^{(0)}`, i.e. `D_{a+c} = a D_1 + D_c`. -/
theorem L1_eq (a : ℚ) : L1 a = a • alpha 1 + L1 0 := by
  apply MvPolynomial.derivation_ext
  intro k
  simp only [Derivation.add_apply, Derivation.smul_apply, L1_X, alpha_X, pc]
  rcases k with _ | _ | k
  · simp
  · simp [C_eq_smul_one]
  · simp

/-- The place `(1, a)` is `L_1` at charge `a`. -/
theorem place_one (a : ℚ) : place 1 a = L1 a := by
  rw [L1_eq, place, one_smul, add_comm]

/-- **`[α_1, L_1^{(0)}] = α_2`**: `[D_1, D_c] = p₂^⊥` on all of `Λ`. -/
theorem alpha_one_L1_zero : ⁅alpha 1, L1 0⁆ = alpha 2 := by
  apply MvPolynomial.derivation_ext
  intro k
  rw [Derivation.commutator_apply]
  rcases k with _ | _ | _ | k
  · simp [L1_X, alpha_X]
  · simp [L1_X, alpha_X, pc]
  · simp [L1_X, alpha_X, pc]
  · simp [L1_X, alpha_X, pc]

/-- **Two places commute iff they are the same point of `P¹`**:
`[D_{(α,β)}, D_{(α',β')}] = (α' β − α β') α_2`. -/
theorem place_comm (α β α' β' : ℚ) :
    ⁅place α β, place α' β'⁆ = (α' * β - α * β') • alpha 2 := by
  refine Derivation.ext fun f => ?_
  have key : alpha 1 (L1 0 f) - L1 0 (alpha 1 f) = alpha 2 f := by
    rw [← Derivation.commutator_apply, alpha_one_L1_zero]
  simp only [Derivation.commutator_apply, place, Derivation.add_apply, Derivation.smul_apply,
    map_add, Derivation.map_smul]
  linear_combination (norm := module) (α' * β - α * β') • key

/-- **`[L_1^{(a)}, L_1^{(b)}] = (a − b) α_2`**: `L_1`s in different charge sectors do not commute. -/
theorem L1_comm (a b : ℚ) : ⁅L1 a, L1 b⁆ = (a - b) • alpha 2 := by
  rw [← place_one, ← place_one, place_comm]
  ring_nf

/-! ## The `sl_2` triple `L_{−1}, L_0, L_1` -/

/-- Virasoro's `L_{−1}` at charge `a`: `a p_1 + Σ_k k p_{k+1} ∂_{p_k}` (not a derivation). -/
noncomputable def Lm1 (a : ℚ) : Module.End ℚ Λ := a • LinearMap.mulLeft ℚ (X 1) + (up : Λ →ₗ[ℚ] Λ)

/-- Virasoro's `L_0` at charge `a`: `a²/2 + Σ_k k p_k ∂_{p_k}`. -/
noncomputable def L0 (a : ℚ) : Module.End ℚ Λ := (a ^ 2 / 2) • 1 + (deg : Λ →ₗ[ℚ] Λ)

theorem L1_up (a : ℚ) : ⁅L1 a, up⁆ = (2 : ℚ) • deg := by
  apply MvPolynomial.derivation_ext
  intro k
  rw [Derivation.commutator_apply]
  rcases k with _ | _ | k
  · simp [L1_X, up_X, deg_X]
  · simp [L1_X, up_X, deg_X, pc]
  · simp [L1_X, up_X, deg_X, pc, Derivation.map_smul, smul_smul]
    module

theorem deg_L1 (a : ℚ) : ⁅deg, L1 a⁆ = -L1 a := by
  apply MvPolynomial.derivation_ext
  intro k
  rw [Derivation.commutator_apply]
  rcases k with _ | _ | k
  · simp [L1_X, deg_X]
  · simp [L1_X, deg_X, pc]
  · simp [L1_X, deg_X, pc, Derivation.map_smul, smul_smul]
    module

theorem deg_up : ⁅deg, up⁆ = up := by
  apply MvPolynomial.derivation_ext
  intro k
  rw [Derivation.commutator_apply]
  simp [up_X, deg_X, Derivation.map_smul, smul_smul]
  module

theorem L1_X_one (a : ℚ) : L1 a (X 1) = C a := by simp [L1_X, pc]

/-- **`[L_1, L_{−1}] = 2 L_0`** at every charge. -/
theorem L1_Lm1 (a : ℚ) :
    (L1 a : Module.End ℚ Λ) * Lm1 a - Lm1 a * (L1 a : Module.End ℚ Λ) = (2 : ℚ) • L0 a := by
  refine LinearMap.ext fun f => ?_
  have h := congrArg (· f) (L1_up a)
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at h
  simp only [Lm1, L0, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_add,
    Derivation.map_smul, Derivation.leibniz, L1_X_one, smul_eq_mul, Module.End.one_apply]
  rw [← sub_eq_zero]
  have hC : f * C a = a • f := by rw [smul_eq_C_mul, mul_comm]
  rw [hC]
  linear_combination (norm := module) h

/-- **`[L_0, L_1] = −L_1`** at every charge. -/
theorem L0_L1 (a : ℚ) :
    L0 a * (L1 a : Module.End ℚ Λ) - (L1 a : Module.End ℚ Λ) * L0 a = -(L1 a : Module.End ℚ Λ) := by
  refine LinearMap.ext fun f => ?_
  have h := congrArg (· f) (deg_L1 a)
  simp only [Derivation.commutator_apply, Derivation.neg_apply] at h
  simp only [L0, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Derivation.coeFn_coe, map_add, Derivation.map_smul,
    Module.End.one_apply, LinearMap.neg_apply]
  linear_combination (norm := module) h

/-- **`[L_0, L_{−1}] = L_{−1}`** at every charge. -/
theorem L0_Lm1 (a : ℚ) : L0 a * Lm1 a - Lm1 a * L0 a = Lm1 a := by
  refine LinearMap.ext fun f => ?_
  have h := congrArg (· f) deg_up
  simp only [Derivation.commutator_apply] at h
  simp only [Lm1, L0, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_add,
    Derivation.map_smul, Derivation.leibniz, deg_X, smul_eq_mul, Module.End.one_apply]
  rw [Nat.cast_one, one_smul, mul_comm f (X 1), Algebra.mul_smul_comm]
  linear_combination (norm := module) h

/-! ## Intertwining derivations along an algebra map -/

/-- If an algebra map `φ` intertwines two derivations on the generators `p_k`, it intertwines
them everywhere. -/
theorem intertwine {B : Type*} [CommRing B] [Algebra ℚ B] (φ : Λ →ₐ[ℚ] B) (D : Der)
    (D' : Derivation ℚ B B) (h : ∀ k, φ (D (X k)) = D' (φ (X k))) (f : Λ) :
    φ (D f) = D' (φ f) := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.derivation_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      Derivation.map_algebraMap, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p k hp =>
    rw [Derivation.leibniz, map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, h, hp, smul_eq_mul, smul_eq_mul]

/-! ## The `ω`-twin: charge reflection -/

/-- `ω` on power sums: `p_k ↦ (−1)^{k−1} p_k`. -/
noncomputable def omega : Λ →ₐ[ℚ] Λ := aeval fun k => ((-1 : ℚ) ^ (k + 1)) • X k

theorem omega_X (k : ℕ) : omega (X k) = ((-1 : ℚ) ^ (k + 1)) • X k := aeval_X _ _

/-- **`ω L_1^{(a)} = −L_1^{(−a)} ω`**: the fermionic twin of `L_1` at charge `a` is `−L_1` at
charge `−a`. -/
theorem omega_L1 (a : ℚ) (f : Λ) : omega (L1 a f) = (-L1 (-a)) (omega f) := by
  refine intertwine omega _ _ (fun k => ?_) f
  rcases k with _ | _ | k
  · simp [L1_X, omega_X]
  · simp [L1_X, omega_X, pc, algHom_C]
  · simp [L1_X, omega_X, pc, Derivation.map_smul, smul_smul, pow_succ]
    ring

/-- **`ω α_2 = −α_2 ω`**: `ω p₂^⊥ = −p₂^⊥ ω`. -/
theorem omega_alpha_two (f : Λ) : omega (alpha 2 f) = (-alpha 2) (omega f) := by
  refine intertwine omega _ _ (fun k => ?_) f
  simp only [alpha_X, omega_X, Derivation.neg_apply, Derivation.map_smul]
  split_ifs with hk
  · subst hk; norm_num
  · simp

theorem omega_deg (f : Λ) : omega (deg f) = deg (omega f) := by
  refine intertwine omega _ _ (fun k => ?_) f
  simp [deg_X, omega_X, Derivation.map_smul, smul_smul]
  ring

theorem omega_up (f : Λ) : omega (up f) = (-up) (omega f) := by
  refine intertwine omega _ _ (fun k => ?_) f
  simp [up_X, omega_X, Derivation.map_smul, smul_smul, pow_succ]
  ring

/-- **`ω L_{−1}^{(a)} = −L_{−1}^{(−a)} ω`**. -/
theorem omega_Lm1 (a : ℚ) (f : Λ) : omega (Lm1 a f) = -(Lm1 (-a) (omega f)) := by
  simp only [Lm1, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, map_smul, map_mul, omega_X, omega_up, Derivation.neg_apply]
  simp
  module

/-- **`ω L_0^{(a)} = L_0^{(−a)} ω`**: the conformal weight `a²/2` of the charged vacuum is
`ω`-invariant. -/
theorem omega_L0 (a : ℚ) (f : Λ) : omega (L0 a f) = L0 (-a) (omega f) := by
  simp only [L0, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Derivation.coeFn_coe, map_add, map_smul, omega_deg, neg_sq]

/-! ## The realisation in `N` variables: the rank is the charge -/

variable (N : ℕ)

/-- `p_k ↦ Σ_i x_i^k` (`p_0 ↦ N`). -/
noncomputable def ev : Λ →ₐ[ℚ] MvPolynomial (Fin N) ℚ := aeval fun k => psum (Fin N) ℚ k

/-- `Σ_i x_i^s ∂/∂x_i`, the derivation sending `x_i` to `x_i^s`. -/
noncomputable def xD (s : ℕ) : Derivation ℚ (MvPolynomial (Fin N) ℚ) (MvPolynomial (Fin N) ℚ) :=
  mkDerivation ℚ fun i => X i ^ s

theorem xD_psum (s k : ℕ) :
    xD N s (psum (Fin N) ℚ (k + 1)) = ((k + 1 : ℕ) : ℚ) • psum (Fin N) ℚ (k + s) := by
  simp only [xD, psum, map_sum, Derivation.leibniz_pow, mkDerivation_X, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_sub_cancel, smul_eq_mul, pow_add, Nat.cast_smul_eq_nsmul ℚ]

/-- **`Σ_i ∂/∂x_i` is `L_1` at charge `N`**: `(Σ_i ∂_{x_i}) ∘ ev = ev ∘ L_1^{(N)}`. -/
theorem ev_L1 (f : Λ) : ev N (L1 N f) = xD N 0 (ev N f) := by
  refine intertwine (ev N) _ _ (fun k => ?_) f
  rcases k with _ | _ | k
  · simp [L1_X, ev]
  · simp only [L1_X, ev, pc, aeval_X]
    rw [xD_psum N 0 0]
    simp
  · simp only [L1_X, ev, pc, aeval_X]
    rw [xD_psum N 0 (k + 1)]
    simp

/-- `Σ_i x_i ∂/∂x_i` is the degree: `(Σ_i x_i ∂_{x_i}) ∘ ev = ev ∘ deg`. -/
theorem ev_deg (f : Λ) : ev N (deg f) = xD N 1 (ev N f) := by
  refine intertwine (ev N) _ _ (fun k => ?_) f
  rcases k with _ | k
  · simp [deg_X, ev]
  · simp only [deg_X, ev, aeval_X, map_smul]
    rw [xD_psum N 1 k]

/-- **`Σ_i x_i² ∂/∂x_i` is `L_{−1}^{(N)} − N p_1`**: `(Σ_i x_i² ∂_{x_i}) ∘ ev = ev ∘ up`. -/
theorem ev_up (f : Λ) : ev N (up f) = xD N 2 (ev N f) := by
  refine intertwine (ev N) _ _ (fun k => ?_) f
  rcases k with _ | k
  · simp [up_X, ev]
  · simp only [up_X, ev, aeval_X, map_smul]
    rw [xD_psum N 2 k]

end RMT.Fock.Virasoro
