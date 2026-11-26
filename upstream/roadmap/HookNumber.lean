import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The hook number of IntegralRepresentationsOfGeneralLinearGroups §1.1 (RMTlib#177, cert 4)

Definitions ported from TauCetiRoadmap ShortGRH / IntegralRepresentationsOfGeneralLinearGroups,
`README.md` §1.1 (a), (b), (g), (i), with the rows of colour `τ` numbered `0, …, N_τ − 1` (so `n_τ = Fin N_τ`):

* (a) variables `y_{(τ,a),i}`, `τ ∈ Φ`, `a < N_τ`, `i ∈ ℕ`; the leading `h × h` minor `Δ_{τ,h}`;
* (b) a weight `κ_τ(h) ≥ 0` (`1 ≤ h < N_τ`), its row lengths `λ_κ(τ, i) = Σ_{i<h<N_τ} κ_τ(h)`;
* (g) `v_κ := ∏_τ ∏_{1≤h<N_τ} Δ_{τ,h}^{κ_τ(h)}`;
* (i) `⟨p, p′⟩_F := Σ_α α! p_α p′_α` and the hook number `H(κ) := ⟨v_κ, v_κ⟩_F`.

Proved here, against Mathlib only:
* `hookNumber_one_row`: **§2.2 (e), first half**. If `κ_τ(h) = 0` for `1 < h < N_τ` and `N_τ > 1` at every `τ`,
  then `H(κ) = ∏_τ κ_τ(1)!`.

The roadmap's remark in §2.2, that `H` is the product of the hook lengths of the diagrams, is checked exactly on 29
weights (one colour, heights `≤ 3`, `|λ| ≤ 8`; RMTlib#177). Its proof is not formalised here.
-/

open MvPolynomial Finset

namespace RoadmapCert.HookNumber

variable {Φ : Type*} (N : Φ → ℕ)

/-- §1.1 (a): the variables `y_{(τ,a),i}`, indexed by `((τ, a), i)`. -/
abbrev Var := (Σ τ : Φ, Fin (N τ)) × ℕ

/-- §1.1 (a): the leading `h × h` minor of the rows of colour `τ` (`1` for `h = 0`; `0` if `h > N_τ`). -/
noncomputable def leadMinor (τ : Φ) (h : ℕ) : MvPolynomial (Var N) ℤ :=
  if hh : h ≤ N τ then
    (Matrix.of fun s t : Fin h => (X (⟨τ, Fin.castLE hh s⟩, (t : ℕ)) : MvPolynomial (Var N) ℤ)).det
  else 0

/-- §1.1 (g): `v_κ = ∏_τ ∏_{1≤h<N_τ} Δ_{τ,h}^{κ_τ(h)}`. -/
noncomputable def vKappa [Fintype Φ] (κ : Φ → ℕ → ℕ) : MvPolynomial (Var N) ℤ :=
  ∏ τ, ∏ h ∈ Ico 1 (N τ), leadMinor N τ h ^ κ τ h

/-- §1.1 (i): the Fock pairing `⟨p, p′⟩_F = Σ_α α! p_α p′_α`. -/
noncomputable def fock {σ : Type*} (p p' : MvPolynomial σ ℤ) : ℤ :=
  ∑ α ∈ p.support, (∏ x ∈ α.support, ((α x).factorial : ℤ)) * p.coeff α * p'.coeff α

/-- §1.1 (i): the hook number `H(κ) = ⟨v_κ, v_κ⟩_F`. -/
noncomputable def hookNumber [Fintype Φ] (κ : Φ → ℕ → ℕ) : ℤ := fock (vKappa N κ) (vKappa N κ)

/-- §1.1 (b): the row lengths `λ_κ(τ, i) = Σ_{i<h<N_τ} κ_τ(h)`. -/
def rowLength (κ : Φ → ℕ → ℕ) (τ : Φ) (i : ℕ) : ℕ := ∑ h ∈ Ioo i (N τ), κ τ h

/-! ## The one-row case (§2.2 (e)) -/

theorem fock_monomial {σ : Type*} (α : σ →₀ ℕ) :
    fock (monomial α (1 : ℤ)) (monomial α 1) = ∏ x ∈ α.support, ((α x).factorial : ℤ) := by
  classical
  unfold fock
  simp [support_monomial, coeff_monomial]

theorem leadMinor_one (τ : Φ) (h1 : 1 ≤ N τ) :
    leadMinor N τ 1 = X (⟨τ, ⟨0, by omega⟩⟩, 0) := by
  rw [leadMinor, dif_pos h1, Matrix.det_unique]
  rfl

/-- The row `0` of colour `τ` (needs `N_τ ≥ 1`). -/
def row0 (hN : ∀ τ, 1 < N τ) (τ : Φ) : Σ τ : Φ, Fin (N τ) := ⟨τ, ⟨0, by have := hN τ; omega⟩⟩

theorem row0_injective (hN : ∀ τ, 1 < N τ) : Function.Injective (row0 N hN) := by
  intro a b h
  exact congrArg Sigma.fst h

theorem hookNumber_one_row [Fintype Φ] [DecidableEq Φ] (κ : Φ → ℕ → ℕ) (hN : ∀ τ, 1 < N τ)
    (hκ : ∀ τ h, 1 < h → h < N τ → κ τ h = 0) :
    hookNumber N κ = ∏ τ, ((κ τ 1).factorial : ℤ) := by
  classical
  set v : Φ → Var N := fun τ => (row0 N hN τ, 0) with hvdef
  have hvinj : Function.Injective v := fun a b h => row0_injective N hN (congrArg Prod.fst h)
  set α : Var N →₀ ℕ := ∑ τ, Finsupp.single (v τ) (κ τ 1) with hα
  -- `v_κ` is the monomial `∏_τ y_{(τ,0),0}^{κ_τ(1)}`
  have hcol : ∀ τ, ∏ h ∈ Ico 1 (N τ), leadMinor N τ h ^ κ τ h = monomial (Finsupp.single (v τ) (κ τ 1)) 1 := by
    intro τ
    rw [prod_eq_single_of_mem 1 (mem_Ico.mpr ⟨le_rfl, hN τ⟩)]
    · rw [leadMinor_one N τ (by have := hN τ; omega), X_pow_eq_monomial]
      rfl
    · intro h hh h1
      have := mem_Ico.mp hh
      rw [hκ τ h (by omega) this.2, pow_zero]
  have hv : vKappa N κ = monomial α 1 := by
    rw [vKappa, hα, monomial_sum_one]
    exact prod_congr rfl fun τ _ => hcol τ
  rw [hookNumber, hv, fock_monomial]
  have hαv : ∀ τ, α (v τ) = κ τ 1 := by
    intro τ
    rw [hα, ← Finsupp.applyAddHom_apply, map_sum, sum_eq_single τ]
    · simp
    · intro b _ hb; rw [Finsupp.applyAddHom_apply, Finsupp.single_apply, if_neg (fun h => hb (hvinj h))]
    · simp
  have hsub : α.support ⊆ univ.image v := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    by_contra hn
    apply hx
    rw [hα, ← Finsupp.applyAddHom_apply, map_sum]
    refine sum_eq_zero fun τ _ => ?_
    rw [Finsupp.applyAddHom_apply, Finsupp.single_apply, if_neg]
    exact fun h => hn (mem_image.mpr ⟨τ, mem_univ _, h⟩)
  rw [prod_subset hsub (fun x _ hx => by rw [Finsupp.notMem_support_iff.mp hx]; simp),
    prod_image (fun a _ b _ h => hvinj h)]
  exact prod_congr rfl fun τ _ => by rw [hαv]

end RoadmapCert.HookNumber
