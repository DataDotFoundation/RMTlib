import RMTlib.Symmetric.JacobiTrudi
import RMTlib.BDTW.Potential
import MeaningLib.Frame.Pattern

/-!
# BDTW, pattern A: the place-uniform (fermionic) form

RMTlib#19 B7, RMTlib#21. At every place `v` the Bump–Diaconis / Tracy–Widom minors are
determinants of `M_v = H_α · diag(ρ_v) · H_βᵀ`, where the sites `l` of a window `W` carry a
**one-body weight** `ρ_v` (`ρ_p(l) = T^l` at a finite place, `ρ_∞(l) = l!` at `∞`) and
`H_α[a, l] = h_{l − a}(α)`. Cauchy–Binet expands the minor over the `N`-element sets of occupied
sites, i.e. over Maya diagrams with `N` particles:

  `det (A · diag ρ · Bᵀ) = Σ_S (∏_{l ∈ S} ρ l) · det A[:, S] · det B[:, S]`   (`det_mul_diagonal_mul_transpose`).

The place enters **only** through the one-body weight `∏_{l ∈ S} ρ l`, so this statement is
place-uniform; its instances at `ρ_∞` and `ρ_p` differ only in `ρ`. With `A = H_α` restricted to the
rows `μ + δ`, the minor `det A[:, S]` is the skew Schur function `s_{λ/μ}(α)` with `S = λ + δ`
(skew Jacobi–Trudi, **lit**, not formalised here). The bosonic corollary (pattern B, `IsExpLinear ρ`)
holds only at `p`.

The statement is tagged `@[frame_pattern]`; the potential role (`archPotential` / `finPotential`,
MeaningLib#4) binds `rhoInf` / `rhoFin`.
-/

namespace RMT.BDTW

open Matrix

variable {R : Type*} [CommRing R]

/-- The one-body weight at `∞`: `ρ_∞(l) = l!`. -/
def rhoInf (l : ℕ) : R := (l.factorial : R)

/-- The one-body weight at a finite place: `ρ_p(l) = T^l`. -/
def rhoFin (T : R) (l : ℕ) : R := T ^ l

/-- Adapter for the potential move `∞ ↦ finite` (MeaningLib#4): its extra explicit binder `T`
becomes a fresh `∀ T` in the twin statement. -/
def infToFin (T : R) : ℕ → R := rhoFin T

/-- Adapter for the potential move `finite ↦ ∞`: the finite weight's `T` is dropped. -/
@[nolint unusedArguments]
def finToInf (_T : R) : ℕ → R := rhoInf

theorem isExpLinear_rhoFin (T : R) : IsExpLinear (rhoFin T) := isExpLinear_pow T

theorem not_isExpLinear_rhoInf [Nontrivial R] : ¬ IsExpLinear (rhoInf (R := R)) :=
  not_isExpLinear_factorial

open Classical in
/-- **Pattern A (place-uniform BDTW)**: Cauchy–Binet with a diagonal one-body weight.
`det (A · diag ρ · Bᵀ) = Σ_S (∏_{l ∈ S} ρ l) · det A[:, S] · det B[:, S]`, the sum over the
`N`-element sets `S` of sites, listed in decreasing order (Maya diagrams with `N` particles). -/
@[frame_pattern]
theorem det_mul_diagonal_mul_transpose {N : ℕ} {W : Type*} [Fintype W] [LinearOrder W]
    (ρ : W → R) (A B : Matrix (Fin N) W R) :
    det (A * diagonal ρ * Bᵀ) = ∑ f : {f : Fin N → W // StrictAnti f},
      (∏ i, ρ (f.1 i)) * det (A.submatrix id f.1) * det (B.submatrix id f.1) := by
  rw [RMT.Symmetric.det_mul_eq_sum_strictAnti]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h1 : (A * diagonal ρ).submatrix id f.1 = A.submatrix id f.1 * diagonal (ρ ∘ f.1) := by
    ext i j
    simp [Matrix.mul_apply, diagonal, Finset.sum_ite_eq']
  have h2 : (Bᵀ).submatrix f.1 id = (B.submatrix id f.1)ᵀ := by
    ext i j
    rfl
  rw [h1, h2, det_mul, det_diagonal, det_transpose]
  simp only [Function.comp_apply]
  ring

end RMT.BDTW
