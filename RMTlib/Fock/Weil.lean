import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Weil's `sl_2` on `V`, the unitary pair, and the fermionic twin

Companion to `bridge/links/virasoro-briefing.md` (W1); checks in `bridge/scripts/weil_sl2.py`. GRH-free.

The original theta lift is built on the Weil (oscillator) representation of the dual pair
`(O(V), SL_2)`. On polynomials on `V = ℚ^m` its `sl_2` is second order:

  `E = ½ Σ x_i²`, `F = ½ Σ ∂_i²`, `H = Σ x_i ∂_i + m/2`,

with `[F, E] = H`, `[H, E] = 2E`, `[H, F] = −2F` (`real_FE`, `real_HE`, `real_HF`). A harmonic polynomial
of degree `j` is a lowest-weight vector of weight `j + m/2` (`real_H_harmonic`); this is the weight of
the Hecke–Schoeneberg theta series. Its `E`-powers have weights `j + m/2 + 2k` (`real_H_E_pow`).

For the unitary pair `(U(m), U(1,1))` (two copies `x, y`, the second the conjugate one):
`E = Σ x_i y_i`, `F = Σ ∂_{x_i} ∂_{y_i}`, `H = Σ (x_i ∂_{x_i} + y_i ∂_{y_i}) + m` (`unit_FE`, `unit_HE`, `unit_HF`).

**Fermionic twin.** On Grassmann variables `ξ_i, η_i` the same formulas give `E = Σ ξ_i η_i`, an even
element. It acts on the span of the products `z_S = ∏_{i∈S} ξ_i η_i` (`z_i² = 0`), with
`E z_S = Σ_{i∉S} z_{S∪i}`, `F = −Σ ∂_{η_i} ∂_{ξ_i}` removing one pair, and `H = 2|S| − m`
(`ferm_FE`, `ferm_HE`, `ferm_HF`). The vacuum has weight `−m` (`ferm_vacuum`), against `+m` for the
bosonic vacuum (`unit_vacuum`). So the shift is `+m`
for bosons and `−m` for fermions: `m/2 ↦ −m/2` per real variable (`m` real fermions pair into `m/2`
complex ones; a single set gives `½ Σ ξ_i² = 0`). This is the boson/fermion twin `N ↦ −N` of the rest of
RMTlib, now on the shift of `H`. The model here is the span of the `z_S` itself (`Finset (Fin m) →₀ ℚ`);
its identification with the even part of an exterior algebra is not formalised.
-/

open MvPolynomial Finset

namespace RMT.Fock.Weil

/-! ## Generic operator calculus on `MvPolynomial σ ℚ` -/

section Generic

variable {σ : Type*}

/-- Multiplication by `g`. -/
noncomputable def mul (g : MvPolynomial σ ℚ) : Module.End ℚ (MvPolynomial σ ℚ) := LinearMap.mulLeft ℚ g

/-- `∂/∂x_i` as an endomorphism. -/
noncomputable def D (i : σ) : Module.End ℚ (MvPolynomial σ ℚ) :=
  (pderiv i : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ))

theorem D_mul (i : σ) (g : MvPolynomial σ ℚ) : D i * mul g = mul g * D i + mul (pderiv i g) := by
  refine LinearMap.ext fun f => ?_
  simp only [D, mul, mul_apply_eq_comp, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
  ring

theorem mul_mul (g h : MvPolynomial σ ℚ) : mul g * mul h = mul (g * h) := by
  refine LinearMap.ext fun f => ?_
  simp [mul]

theorem mul_zero' : mul (0 : MvPolynomial σ ℚ) = 0 := LinearMap.ext fun f => by simp [mul]

theorem mul_one' : mul (1 : MvPolynomial σ ℚ) = 1 := LinearMap.ext fun f => by simp [mul]

theorem mul_add' (g h : MvPolynomial σ ℚ) : mul (g + h) = mul g + mul h :=
  LinearMap.ext fun f => by simp [mul, add_mul]

theorem mul_smul' (c : ℚ) (g : MvPolynomial σ ℚ) : mul (c • g) = c • mul g :=
  LinearMap.ext fun f => by simp [mul]

theorem mul_sum' {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial σ ℚ) :
    mul (∑ i ∈ s, g i) = ∑ i ∈ s, mul (g i) := by
  refine LinearMap.ext fun f => ?_
  simp [mul, Finset.sum_mul]

theorem mul_natCast (n : ℕ) : mul (n : MvPolynomial σ ℚ) = (n : ℚ) • (1 : Module.End ℚ _) :=
  LinearMap.ext fun f => by simp [mul, Nat.cast_smul_eq_nsmul]

theorem D_D_comm [DecidableEq σ] (i j : σ) : D i * D j = D j * (D i : Module.End ℚ (MvPolynomial σ ℚ)) := by
  have h : ⁅(pderiv i : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ)), pderiv j⁆ = 0 :=
    MvPolynomial.derivation_ext fun v => by
      rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
      simp only [Pi.single_apply]; split_ifs <;> simp
  have h2 := congrArg (fun T : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) =>
    ((T : Derivation ℚ _ _) : Module.End ℚ (MvPolynomial σ ℚ))) h
  simp only [Derivation.commutator_coe_linear_map, Ring.lie_def] at h2
  unfold D
  exact sub_eq_zero.mp (by simpa using h2)

variable [Fintype σ] [DecidableEq σ]

/-- The Euler operator `Σ_v x_v ∂_v` (the degree). -/
noncomputable def eulerG : Module.End ℚ (MvPolynomial σ ℚ) := ∑ v, mul (X v) * D v

omit [Fintype σ] [DecidableEq σ] in
theorem sum_comm_sub {ι : Type*} (s : Finset ι) (A : ι → Module.End ℚ (MvPolynomial σ ℚ))
    (B : Module.End ℚ (MvPolynomial σ ℚ)) :
    (∑ i ∈ s, A i) * B - B * ∑ i ∈ s, A i = ∑ i ∈ s, (A i * B - B * A i) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

omit [Fintype σ] [DecidableEq σ] in
theorem mul_comm' (g h : MvPolynomial σ ℚ) : mul g * mul h = mul h * mul g := by
  rw [mul_mul, mul_mul, mul_comm]

omit [DecidableEq σ] in
/-- **`[Σ x ∂, g] = n g` for `g` homogeneous of degree `n`** (Euler's identity). -/
theorem eulerG_mul_hom {g : MvPolynomial σ ℚ} {n : ℕ} (hg : g.IsHomogeneous n) :
    eulerG * mul g - mul g * eulerG = (n : ℚ) • mul g := by
  rw [eulerG, sum_comm_sub]
  have : ∀ v, mul (X v) * D v * mul g - mul g * (mul (X v) * D v) = mul (X v * pderiv v g) := by
    intro v
    rw [mul_assoc, D_mul, mul_add, ← mul_assoc, ← mul_assoc, mul_comm' (X v) g, mul_mul, mul_mul]
    abel
  rw [Finset.sum_congr rfl fun v _ => this v, ← mul_sum', hg.sum_X_mul_pderiv,
    ← Nat.cast_smul_eq_nsmul ℚ, mul_smul']

omit [Fintype σ] in
theorem D_X' (a v : σ) : D a * mul (X v) = mul (X v) * D a + if a = v then 1 else 0 := by
  rw [D_mul, pderiv_X]
  by_cases h : a = v
  · subst h; simp [mul_one']
  · simp [h, Ne.symm h, mul_zero']

/-- **`[Σ x ∂, ∂_a ∂_b] = −2 ∂_a ∂_b`**: second-order derivatives have degree `−2`. -/
theorem eulerG_DD (a b : σ) :
    eulerG * (D a * D b) - D a * D b * eulerG = (-2 : ℚ) • (D a * D b) := by
  rw [eulerG, sum_comm_sub]
  have : ∀ v, mul (X v) * D v * (D a * D b) - D a * D b * (mul (X v) * D v) =
      -((if a = v then D b * D v else 0) + (if b = v then D a * D v else 0)) := by
    intro v
    have h1 : D a * D b * mul (X v) =
        mul (X v) * D a * D b + (if a = v then 1 else 0) * D b + D a * (if b = v then 1 else 0) := by
      rw [mul_assoc, D_X', mul_add, ← mul_assoc, D_X', add_mul]
    have hc : D v * D a * D b = D a * D b * D v := by
      rw [D_D_comm v a, mul_assoc, D_D_comm v b, ← mul_assoc]
    rw [show mul (X v) * D v * (D a * D b) - D a * D b * (mul (X v) * D v) =
        mul (X v) * (D v * D a * D b) - (D a * D b * mul (X v)) * D v by simp only [mul_assoc], h1, hc]
    split_ifs <;> simp only [add_mul, mul_assoc, one_mul, mul_one, zero_mul, mul_zero, add_zero] <;>
      abel
  rw [Finset.sum_congr rfl fun v _ => this v, Finset.sum_neg_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq, ite_eq_left (mem_univ _), ite_eq_left (mem_univ _), D_D_comm b a]
  module

end Generic

/-! ## The real pair `(O(m), SL_2)` -/

section Real

variable (m : ℕ)

/-- `|x|² = Σ x_i²`. -/
noncomputable def normSq : MvPolynomial (Fin m) ℚ := ∑ i, X i ^ 2

/-- The Euler operator `Σ x_i ∂_i`. -/
noncomputable def euler : Module.End ℚ (MvPolynomial (Fin m) ℚ) := ∑ i, mul (X i) * D i

/-- `E = ½ |x|²`. -/
noncomputable def E : Module.End ℚ (MvPolynomial (Fin m) ℚ) := (1 / 2 : ℚ) • mul (normSq m)

/-- `F = ½ Σ ∂_i²` (half the Laplacian). -/
noncomputable def F : Module.End ℚ (MvPolynomial (Fin m) ℚ) := (1 / 2 : ℚ) • ∑ i, D i * D i

/-- `H = Σ x_i ∂_i + m/2`. -/
noncomputable def H : Module.End ℚ (MvPolynomial (Fin m) ℚ) := euler m + ((m : ℚ) / 2) • 1

theorem pderiv_normSq (i : Fin m) : pderiv i (normSq m) = 2 * X i := by
  simp [normSq, map_sum, pderiv_X, Pi.single_apply, mul_comm]

theorem D_X (i j : Fin m) :
    D i * mul (X j) = mul (X j) * D i + if i = j then 1 else 0 := by
  rw [D_mul, pderiv_X]
  by_cases h : i = j
  · subst h; simp [mul_one']
  · simp [h, Ne.symm h, mul_zero']

/-- `∂_i² |x|² = |x|² ∂_i² + 4 x_i ∂_i + 2`. -/
theorem DD_normSq (i : Fin m) :
    D i * D i * mul (normSq m) =
      mul (normSq m) * D i * D i + (4 : ℚ) • (mul (X i) * D i) + (2 : ℚ) • 1 := by
  have h1 := D_mul i (normSq m)
  rw [pderiv_normSq, show (2 : MvPolynomial (Fin m) ℚ) * X i = (2 : ℚ) • X i by
    rw [smul_eq_C_mul]; rfl, mul_smul'] at h1
  have h2 := D_X m i i
  rw [ite_eq_left rfl] at h2
  rw [mul_assoc, h1, mul_add, ← mul_assoc, h1, mul_smul_comm, h2]
  simp only [add_mul, smul_mul_assoc, smul_add, mul_assoc]
  module

theorem sum_mul_sub (A : Fin m → Module.End ℚ (MvPolynomial (Fin m) ℚ)) (B : Module.End ℚ _) :
    (∑ i, A i) * B - B * ∑ i, A i = ∑ i, (A i * B - B * A i) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- **`[F, E] = H`**. -/
theorem real_FE : F m * E m - E m * F m = H m := by
  have key : ∀ i, D i * D i * mul (normSq m) - mul (normSq m) * (D i * D i) =
      (4 : ℚ) • (mul (X i) * D i) + (2 : ℚ) • 1 := fun i => by
    rw [DD_normSq, mul_assoc (mul (normSq m)) (D i) (D i)]; abel
  have e : F m * E m - E m * F m =
      ((1 / 2 : ℚ) * (1 / 2)) • ((∑ i, D i * D i) * mul (normSq m) - mul (normSq m) * ∑ i, D i * D i) := by
    simp only [F, E, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
  rw [e, sum_mul_sub, Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib,
    Finset.sum_const, card_univ, Fintype.card_fin, ← Finset.smul_sum, H, euler]
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  module

theorem normSq_isHomogeneous : (normSq m).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _

theorem euler_eq : euler m = eulerG := rfl

theorem const_comm (c : ℚ) (A : Module.End ℚ (MvPolynomial (Fin m) ℚ)) :
    (c • (1 : Module.End ℚ _)) * A - A * (c • 1) = 0 := by
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one, sub_self]

/-- **`[H, E] = 2E`**. -/
theorem real_HE : H m * E m - E m * H m = (2 : ℚ) • E m := by
  have h := eulerG_mul_hom (normSq_isHomogeneous m)
  have hc := const_comm m ((m : ℚ) / 2) (E m)
  simp only [H, add_mul, mul_add] at hc ⊢
  rw [show euler m * E m + ((m : ℚ) / 2) • 1 * E m - (E m * euler m + E m * ((m : ℚ) / 2) • 1) =
    (euler m * E m - E m * euler m) + (((m : ℚ) / 2) • 1 * E m - E m * ((m : ℚ) / 2) • 1) by abel,
    hc, add_zero]
  rw [show euler m * E m - E m * euler m =
      (1 / 2 : ℚ) • (eulerG * mul (normSq m) - mul (normSq m) * eulerG) by
    simp only [E, euler_eq, mul_smul_comm, smul_mul_assoc, smul_sub], h, E]
  push_cast
  module

/-- **`[H, F] = −2F`**. -/
theorem real_HF : H m * F m - F m * H m = (-2 : ℚ) • F m := by
  have hc := const_comm m ((m : ℚ) / 2) (F m)
  simp only [H, add_mul, mul_add] at hc ⊢
  rw [show euler m * F m + ((m : ℚ) / 2) • 1 * F m - (F m * euler m + F m * ((m : ℚ) / 2) • 1) =
    (euler m * F m - F m * euler m) + (((m : ℚ) / 2) • 1 * F m - F m * ((m : ℚ) / 2) • 1) by abel,
    hc, add_zero]
  simp only [F, mul_smul_comm, smul_mul_assoc, euler_eq, Finset.mul_sum, Finset.sum_mul]
  rw [show ∀ (c : ℚ) (A B : Module.End ℚ (MvPolynomial (Fin m) ℚ)), c • A - c • B = c • (A - B) from
    fun c A B => (smul_sub c A B).symm, ← Finset.sum_sub_distrib]
  simp only [eulerG_DD]
  rw [← Finset.smul_sum, smul_smul, smul_smul]
  norm_num

/-- A polynomial is **harmonic** if `F` (half the Laplacian) kills it. -/
def IsHarmonic (h : MvPolynomial (Fin m) ℚ) : Prop := F m h = 0

/-- **Harmonic polynomials are lowest-weight vectors of weight `j + m/2`**: `F h = 0` and
`H h = (j + m/2) h` for `h` harmonic and homogeneous of degree `j`. -/
theorem real_H_harmonic {h : MvPolynomial (Fin m) ℚ} {j : ℕ} (hh : h.IsHomogeneous j)
    (hF : IsHarmonic m h) : F m h = 0 ∧ H m h = ((j : ℚ) + m / 2) • h := by
  refine ⟨hF, ?_⟩
  have e : euler m h = ∑ i, X i * pderiv i h := by
    simp [euler, mul, D]
  simp only [H, LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self, e,
    hh.sum_X_mul_pderiv, ← Nat.cast_smul_eq_nsmul ℚ, add_smul]

/-- **The `E`-tower over a weight vector**: `H (E^k h) = (w + 2k) E^k h` if `H h = w h`. -/
theorem real_H_E_pow {h : MvPolynomial (Fin m) ℚ} {w : ℚ} (hh : H m h = w • h) (k : ℕ) :
    H m ((E m ^ k) h) = (w + 2 * k) • (E m ^ k) h := by
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    have hHE := congrArg (· ((E m ^ k) h)) (real_HE m)
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply] at hHE
    rw [pow_succ', mul_apply_eq_comp, sub_eq_iff_eq_add.mp hHE, ih, map_smul]
    push_cast
    module

end Real

/-! ## The unitary pair `(U(m), U(1,1))` -/

section Unitary

variable (m : ℕ)

/-- `Σ_i x_i y_i` on `ℚ[x, y]` (`x = inl`, `y = inr`, the conjugate copy). -/
noncomputable def pairing : MvPolynomial (Fin m ⊕ Fin m) ℚ := ∑ i, X (Sum.inl i) * X (Sum.inr i)

/-- `E = Σ x_i y_i`. -/
noncomputable def uE : Module.End ℚ (MvPolynomial (Fin m ⊕ Fin m) ℚ) := mul (pairing m)

/-- `F = Σ ∂_{x_i} ∂_{y_i}`. -/
noncomputable def uF : Module.End ℚ (MvPolynomial (Fin m ⊕ Fin m) ℚ) :=
  ∑ i, D (Sum.inl i) * D (Sum.inr i)

/-- `H = Σ (x ∂_x + y ∂_y) + m`. -/
noncomputable def uH : Module.End ℚ (MvPolynomial (Fin m ⊕ Fin m) ℚ) := eulerG + (m : ℚ) • 1

theorem pairing_isHomogeneous : (pairing m).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X _ _).mul (isHomogeneous_X _ _)

theorem pderiv_inl_pairing (i : Fin m) : pderiv (Sum.inl i) (pairing m) = X (Sum.inr i) := by
  simp [pairing, map_sum, pderiv_X, Pi.single_apply]

theorem pderiv_inr_pairing (i : Fin m) : pderiv (Sum.inr i) (pairing m) = X (Sum.inl i) := by
  simp [pairing, map_sum, pderiv_X, Pi.single_apply]

/-- **`[F, E] = H`** for the unitary pair. -/
theorem unit_FE : uF m * uE m - uE m * uF m = uH m := by
  rw [uF, uE, sum_comm_sub]
  have : ∀ i : Fin m, D (Sum.inl i) * D (Sum.inr i) * mul (pairing m) -
      mul (pairing m) * (D (Sum.inl i) * D (Sum.inr i)) =
      mul (X (Sum.inl i)) * D (Sum.inl i) + mul (X (Sum.inr i)) * D (Sum.inr i) + 1 := by
    intro i
    have hb := D_mul (Sum.inr i) (pairing m)
    have ha := D_mul (Sum.inl i) (pairing m)
    have hx := D_X' (σ := Fin m ⊕ Fin m) (Sum.inl i) (Sum.inl i)
    rw [pderiv_inr_pairing] at hb
    rw [pderiv_inl_pairing] at ha
    rw [ite_eq_left rfl] at hx
    rw [mul_assoc, hb, mul_add, ← mul_assoc, ha, hx, add_mul, mul_assoc]
    abel
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, card_univ, Fintype.card_fin, uH, eulerG, Fintype.sum_sum_type,
    ← Nat.cast_smul_eq_nsmul ℚ]

/-- **`[H, E] = 2E`** for the unitary pair. -/
theorem unit_HE : uH m * uE m - uE m * uH m = (2 : ℚ) • uE m := by
  have h := eulerG_mul_hom (pairing_isHomogeneous m)
  simp only [uH, uE, add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  rw [show eulerG * mul (pairing m) + (m : ℚ) • mul (pairing m) -
      (mul (pairing m) * eulerG + (m : ℚ) • mul (pairing m)) =
      eulerG * mul (pairing m) - mul (pairing m) * eulerG by abel, h]
  norm_num

/-- **`[H, F] = −2F`** for the unitary pair. -/
theorem unit_HF : uH m * uF m - uF m * uH m = (-2 : ℚ) • uF m := by
  simp only [uH, uF, add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  rw [show eulerG * (∑ i, D (Sum.inl i) * D (Sum.inr i)) +
      (m : ℚ) • (∑ i : Fin m, D (Sum.inl i) * D (Sum.inr i)) -
      ((∑ i, D (Sum.inl i) * D (Sum.inr i)) * eulerG +
        (m : ℚ) • (∑ i : Fin m, D (Sum.inl i) * D (Sum.inr i))) =
      eulerG * (∑ i, D (Sum.inl i) * D (Sum.inr i)) -
        (∑ i, D (Sum.inl i) * D (Sum.inr i)) * eulerG by abel]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [eulerG_DD, ← Finset.smul_sum]

/-- **The bosonic vacuum** `1` is killed by `F` and has weight `+m` (the twin of `ferm_vacuum`). -/
theorem unit_vacuum : uF m 1 = 0 ∧ uH m 1 = (m : ℚ) • 1 := by
  refine ⟨?_, ?_⟩
  · simp [uF, D]
  · simp [uH, eulerG, D, mul]

end Unitary

/-! ## The fermionic twin: pairs of Grassmann variables -/

section Fermion

variable (m : ℕ)

/-- The span of the even products `z_S = ∏_{i∈S} ξ_i η_i` (`z_i² = 0`), indexed by subsets. -/
abbrev Ferm := Finset (Fin m) →₀ ℚ

/-- `E = Σ_i ξ_i η_i`: `z_S ↦ Σ_{i∉S} z_{S∪i}`. -/
noncomputable def fE : Module.End ℚ (Ferm m) :=
  Finsupp.linearCombination ℚ fun S => ∑ i, if i ∈ S then 0 else Finsupp.single (insert i S) (1 : ℚ)

/-- `F = −Σ_i ∂_{η_i} ∂_{ξ_i}`: `z_S ↦ −Σ_{i∈S} z_{S∖i}`. -/
noncomputable def fF : Module.End ℚ (Ferm m) :=
  Finsupp.linearCombination ℚ fun S => -∑ i, if i ∈ S then Finsupp.single (S.erase i) (1 : ℚ) else 0

/-- `H = 2|S| − m`, i.e. `N_ξ + N_η − m`. -/
noncomputable def fH : Module.End ℚ (Ferm m) :=
  Finsupp.linearCombination ℚ fun S => (2 * (S.card : ℚ) - m) • Finsupp.single S (1 : ℚ)

theorem fE_single (S : Finset (Fin m)) :
    fE m (Finsupp.single S 1) = ∑ i, if i ∈ S then 0 else Finsupp.single (insert i S) 1 := by
  simp [fE]

theorem fF_single (S : Finset (Fin m)) :
    fF m (Finsupp.single S 1) = -∑ i, if i ∈ S then Finsupp.single (S.erase i) 1 else 0 := by
  simp [fF]

theorem fH_single (S : Finset (Fin m)) :
    fH m (Finsupp.single S 1) = (2 * (S.card : ℚ) - m) • Finsupp.single S 1 := by
  simp [fH]

theorem ext_single {A B : Module.End ℚ (Ferm m)}
    (h : ∀ S, A (Finsupp.single S 1) = B (Finsupp.single S 1)) : A = B := by
  refine Finsupp.lhom_ext fun S c => ?_
  have h1 : Finsupp.single S c = c • Finsupp.single S (1 : ℚ) := by simp
  rw [h1, map_smul, map_smul, h]

theorem card_filter_mem (S : Finset (Fin m)) :
    (∑ i : Fin m, if i ∈ S then (1 : ℚ) else 0) = S.card := by
  rw [Finset.sum_boole]; simp

theorem fF_fE (S : Finset (Fin m)) :
    fF m (fE m (Finsupp.single S 1)) = -∑ i, ∑ j, (if i ∈ S then (0 : Ferm m) else
      if j ∈ insert i S then Finsupp.single ((insert i S).erase j) 1 else 0) := by
  rw [fE_single, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · simp
  · rw [fF_single]

theorem fE_fF (S : Finset (Fin m)) :
    fE m (fF m (Finsupp.single S 1)) = -∑ i, ∑ j, (if j ∈ S then
      (if i ∈ S.erase j then (0 : Ferm m) else Finsupp.single (insert i (S.erase j)) 1) else 0) := by
  rw [fF_single, map_neg, map_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [fE_single]
  · simp

theorem ferm_key (S : Finset (Fin m)) (i j : Fin m) :
    (if j ∈ S then (if i ∈ S.erase j then (0 : Ferm m) else
        Finsupp.single (insert i (S.erase j)) 1) else 0) -
      (if i ∈ S then (0 : Ferm m) else
        if j ∈ insert i S then Finsupp.single ((insert i S).erase j) 1 else 0) =
      if i = j then ((if i ∈ S then (1 : ℚ) else 0) - (if i ∈ S then 0 else 1)) • Finsupp.single S 1
        else 0 := by
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ S
    · simp [hi, Finset.insert_erase hi]
    · simp [hi, Finset.erase_insert hi]
  · have h1 : (insert i S).erase j = insert i (S.erase j) := Finset.erase_insert_of_ne hij
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [hi, hj, hij, Ne.symm hij, h1, Finset.mem_erase]

/-- **`[F, E] = H`** on the fermionic pairs: the shift is `−m`. -/
theorem ferm_FE : fF m * fE m - fE m * fF m = fH m := by
  apply ext_single
  intro S
  rw [LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, fF_fE, fE_fF, fH_single,
    neg_sub_neg, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ferm_key, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.sum_smul]
  congr 1
  rw [Finset.sum_sub_distrib, card_filter_mem]
  have : (∑ i : Fin m, if i ∈ S then (0 : ℚ) else 1) = m - S.card := by
    have h := card_filter_mem m S
    have h2 : (∑ i : Fin m, ((if i ∈ S then (1 : ℚ) else 0) + (if i ∈ S then 0 else 1))) = m := by
      simp only [show ∀ i : Fin m, ((if i ∈ S then (1 : ℚ) else 0) + (if i ∈ S then 0 else 1)) = 1 from
        fun i => by split_ifs <;> norm_num, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
    rw [Finset.sum_add_distrib, h] at h2
    linarith
  rw [this]; ring

/-- **`[H, E] = 2E`** on the fermionic pairs. -/
theorem ferm_HE : fH m * fE m - fE m * fH m = (2 : ℚ) • fE m := by
  apply ext_single
  intro S
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply, fE_single, map_sum,
    fH_single, map_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · simp
  · rw [fH_single, Finset.card_insert_of_notMem hi]
    push_cast
    module

/-- **`[H, F] = −2F`** on the fermionic pairs. -/
theorem ferm_HF : fH m * fF m - fF m * fH m = (-2 : ℚ) • fF m := by
  apply ext_single
  intro S
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply, fF_single, map_neg,
    map_sum, fH_single, map_smul, Finset.smul_sum, smul_neg, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib, neg_sub_neg]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [fH_single, Finset.card_erase_of_mem hi]
    have : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
    push_cast [this]
    module
  · simp

/-- **The fermionic vacuum** `z_∅ = 1` is killed by `F` and has weight `−m`. -/
theorem ferm_vacuum : fF m (Finsupp.single ∅ 1) = 0 ∧
    fH m (Finsupp.single ∅ 1) = (-(m : ℚ)) • Finsupp.single ∅ 1 := by
  refine ⟨?_, ?_⟩
  · rw [fF_single]; simp
  · rw [fH_single]; simp

end Fermion

end RMT.Fock.Weil
