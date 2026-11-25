import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Module.LinearMap.End
import MeaningLib.Frame.Pattern

/-!
# One API for theta lifts: a kernel and a period

Moved from RH-Dual (`RHDual.Theta.Kernel`, RMTlib#7): RH-Dual's `bridge/links/theta-api.md` is the
companion, and RH-Dual's `bridge/RHDualBridge/ThetaAPI.lean` restates the GRH proof's live lift
definitions as instances. GRH-free: imports Mathlib only (and MeaningLib for the pattern tag).

Alpöge's GRH proof defines its theta lifts many times over (RH-Dual's `bridge/scripts/theta_census.py`).
Every live definition factors through two independent choices:

* a **kernel** (`ThetaKernel`): an action `act` of a pair of groups `G × H` on test functions `S`,
  landing in some space `T`, followed by a read-out `read : T → ℂ`. The proof uses two read-outs:
  evaluation at `0` in a model where test functions are already theta functions (`thetaKO`), and
  the sum over rational points of a Schwartz function (`thetaSum`, and the `∑'` of `StdUnn.theta`);
* a **period** (`per : (G → ℂ) → ℂ`): what is done with `g ↦ ker Φ g h`. The proof uses the
  integral over a fundamental domain (`perOn`), the average over an automorphic quotient, the
  Petersson pairing against a form, and, once, a definition by choice (`factor`).

`ThetaKernel.lift per Φ h = per (fun g => ker Φ g h)` is then every lift; `swap` exchanges the two
members of the dual pair, so lifts in the other direction are the same API.

The one shared argument (`ker_automorphic`): if the action is a monoid hom `ω` on `S` and the
read-out is invariant under `ω γ` for `γ` in a set `Γ` on test functions in a stable set `A`, the
kernel is left `Γ`-invariant on `A`. The proof re-derives this inline at each use of `thetaKO`
(`om_aut … (om_pres …)`); here it is proved once, for any read-out.

**ω-twin.** The API does not mention statistics: `S`, `act`, `read` are data. The fermionic twin of an
instance is the same API with `S` a Clifford (exterior) module and `read` the vacuum coefficient,
as in `RMT.Fock.Weil` (`ferm_*`); the proof has no fermionic theta lift, so no bridge instance exists.

**Checker.** `ker_intertwine` is tagged `@[frame_pattern theta]`: a change of model that intertwines
the actions and matches the read-outs gives equal kernels. Alpöge's proof has an instance,
`GlobalTheory.TripleRead.IsTransp` with `τ = σ = thO` (RH-Dual `bridge/links/thk-d7.md`), which is the
theta-side calibration of MeaningLib#11.
-/

namespace RMT.Fock

open MeasureTheory

/-- A theta kernel: an action of `G × H` on test functions `S`, with values in `T`, and a read-out. -/
structure ThetaKernel (G H S T : Type*) where
  /-- The (Weil-type) action of the pair. -/
  act : G × H → S → T
  /-- The read-out: evaluation at `0`, or a sum over rational points. -/
  read : T → ℂ

namespace ThetaKernel

variable {G H S T : Type*}

/-- The kernel `θ_Φ(g, h) = read (act (g, h) Φ)`. -/
def ker (K : ThetaKernel G H S T) (Φ : S) (g : G) (h : H) : ℂ := K.read (K.act (g, h) Φ)

/-- The same kernel with the roles of the two groups exchanged. -/
def swap (K : ThetaKernel G H S T) : ThetaKernel H G S T where
  act p := K.act (p.2, p.1)
  read := K.read

@[simp] theorem ker_swap (K : ThetaKernel G H S T) (Φ : S) (g : G) (h : H) :
    K.swap.ker Φ h g = K.ker Φ g h := rfl

theorem swap_swap (K : ThetaKernel G H S T) : K.swap.swap = K := rfl

/-- The theta lift of `Φ` along `G` for a period functional `per` on functions on `G`. -/
def lift (K : ThetaKernel G H S T) (per : (G → ℂ) → ℂ) (Φ : S) (h : H) : ℂ :=
  per (fun g => K.ker Φ g h)

/-- Integral over a set (a fundamental domain) as a period. -/
noncomputable def perOn [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) (F : G → ℂ) : ℂ := ∫ g in 𝓕, F g ∂μ

theorem lift_perOn [MeasurableSpace G] (K : ThetaKernel G H S T) (μ : Measure G) (𝓕 : Set G)
    (Φ : S) (h : H) : K.lift (perOn μ 𝓕) Φ h = ∫ g in 𝓕, K.ker Φ g h ∂μ := rfl

/-- A period multiplied by a form `f` before integrating: `per (F · f)`. -/
def perAgainst (per : (G → ℂ) → ℂ) (f : G → ℂ) (F : G → ℂ) : ℂ := per (fun g => F g * f g)

/-- Lift by factorisation through the kernel map `κ`: the linear map `q` on the span of the kernels
with `q (κ Ψ) = pD Ψ` on `Ψ ∈ A`, if one exists (chosen), else `0`. -/
noncomputable def factor {V P : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]
    (κ : S → V) (A : Set S) (pD : S → P) : V →ₗ[ℂ] P :=
  open Classical in
  if hq : ∃ q : V →ₗ[ℂ] P, ∀ Ψ ∈ A, q (κ Ψ) = pD Ψ then hq.choose else 0

theorem factor_spec {V P : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]
    (κ : S → V) (A : Set S) (pD : S → P) (hq : ∃ q : V →ₗ[ℂ] P, ∀ Ψ ∈ A, q (κ Ψ) = pD Ψ) :
    ∀ Ψ ∈ A, factor κ A pD (κ Ψ) = pD Ψ := by
  classical
  unfold factor
  rw [dif_pos hq]
  exact hq.choose_spec

/-- **Change of model.** If `τ` carries test functions of `K` to those of `K'`, intertwining the
actions up to `σ` and group maps `gG`, `gH`, and the read-outs agree through `σ`, then the kernels
agree: `θ'_{τ Φ}(g, h) = θ_Φ(gG g, gH h)`. -/
@[frame_pattern theta]
theorem ker_intertwine {G' H' S' T' : Type*} (K : ThetaKernel G H S T) (K' : ThetaKernel G' H' S' T')
    (τ : S → S') (σ : T → T') (gG : G' → G) (gH : H' → H) (A : Set S)
    (hact : ∀ Φ ∈ A, ∀ g h, K'.act (g, h) (τ Φ) = σ (K.act (gG g, gH h) Φ))
    (hread : ∀ Ψ, K'.read (σ Ψ) = K.read Ψ) {Φ : S} (hΦ : Φ ∈ A) (g : G') (h : H') :
    K'.ker (τ Φ) g h = K.ker Φ (gG g) (gH h) := by
  unfold ker
  rw [hact Φ hΦ g h, hread]

/-! ### Kernels from a monoid action -/

section Hom

variable [Monoid G] [Monoid H] [AddCommMonoid S] [Module ℂ S]

/-- The kernel of a linear action `ω` of `G × H` on `S` with read-out `read`. -/
def ofEnd (ω : G × H →* Module.End ℂ S) (read : S → ℂ) : ThetaKernel G H S S where
  act p Φ := ω p Φ
  read := read

theorem ker_ofEnd (ω : G × H →* Module.End ℂ S) (read : S → ℂ) (Φ : S) (g : G) (h : H) :
    (ofEnd ω read).ker Φ g h = read (ω (g, h) Φ) := rfl

/-- For a linear read-out the kernel at `(g, h)` is a linear form on test functions. -/
def kerL (ω : G × H →* Module.End ℂ S) (read : S →ₗ[ℂ] ℂ) (g : G) (h : H) : S →ₗ[ℂ] ℂ :=
  read ∘ₗ ω (g, h)

theorem kerL_apply (ω : G × H →* Module.End ℂ S) (read : S →ₗ[ℂ] ℂ) (g : G) (h : H) (Φ : S) :
    kerL ω read g h Φ = (ofEnd ω read).ker Φ g h := rfl

/-- Cocycle: moving a right factor of `(g, h)` onto the test function. -/
theorem ker_ofEnd_mul (ω : G × H →* Module.End ℂ S) (read : S → ℂ) (Φ : S) (g g' : G)
    (h h' : H) : (ofEnd ω read).ker Φ (g * g') (h * h') = (ofEnd ω read).ker (ω (g', h') Φ) g h := by
  simp only [ker_ofEnd]
  rw [show ((g * g', h * h') : G × H) = (g, h) * (g', h') from rfl, map_mul]
  rfl

/-- **Automorphy of the theta kernel**, one argument for every read-out: if `A` is stable under `ω`
and `read ∘ ω γ = read` on `A` for `γ ∈ Γ`, then `θ_Φ(γ₁ g, γ₂ h) = θ_Φ(g, h)` for `Φ ∈ A`. -/
theorem ker_automorphic (ω : G × H →* Module.End ℂ S) (read : S → ℂ) (A : Set S)
    (Γ : Set (G × H)) (hA : ∀ p Φ, Φ ∈ A → ω p Φ ∈ A)
    (hread : ∀ γ ∈ Γ, ∀ Φ ∈ A, read (ω γ Φ) = read Φ) {γ : G × H} (hγ : γ ∈ Γ) {Φ : S}
    (hΦ : Φ ∈ A) (g : G) (h : H) :
    (ofEnd ω read).ker Φ (γ.1 * g) (γ.2 * h) = (ofEnd ω read).ker Φ g h := by
  simp only [ker_ofEnd]
  rw [show ((γ.1 * g, γ.2 * h) : G × H) = γ * (g, h) from rfl, map_mul, Module.End.mul_apply]
  exact hread γ hγ _ (hA _ _ hΦ)

/-- The lift of an automorphic kernel is unchanged by translating `h` by the second component of
`γ ∈ Γ`, for any period `per` that is invariant under left translation by `γ.1`. -/
theorem lift_automorphic (ω : G × H →* Module.End ℂ S) (read : S → ℂ) (A : Set S)
    (Γ : Set (G × H)) (hA : ∀ p Φ, Φ ∈ A → ω p Φ ∈ A)
    (hread : ∀ γ ∈ Γ, ∀ Φ ∈ A, read (ω γ Φ) = read Φ) {γ : G × H} (hγ : γ ∈ Γ)
    (per : (G → ℂ) → ℂ) (hper : ∀ F : G → ℂ, per (fun g => F (γ.1 * g)) = per F) {Φ : S}
    (hΦ : Φ ∈ A) (h : H) : (ofEnd ω read).lift per Φ (γ.2 * h) = (ofEnd ω read).lift per Φ h := by
  unfold lift
  rw [← hper]
  congr 1
  funext g
  exact ker_automorphic ω read A Γ hA hread hγ hΦ g h

end Hom

end ThetaKernel

end RMT.Fock
