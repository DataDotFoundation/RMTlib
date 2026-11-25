import RMTlib.Tableaux.HookLengthFormula
import RMTlib.Symmetric.JacobiTrudi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Edges of random partitions: the statements (RMTlib#53, #19)

Precise statements, as `Prop`s, of what is known or conjectured at the **edges** of random
partitions. No proofs: these are targets (repo convention: unproved targets are `Prop`s, no `sorry`).
Each statement is tagged **lit** (published), **computed** (RMTlib's own exact numerics) or
**conjecture**. The objects are all finite and explicit; the only limits are `Filter.Tendsto`.

## Soft edge (Plancherel, no wall)
* `PlancherelNormalised` (lit; equivalent to `Σ (f^λ)² = n!`): the Plancherel weights `(f^λ)²/n!`
  form a probability measure on partitions of `n`.
* `RSKLongestIncreasing` (lit, Schensted): the number of permutations of `n` whose longest
  increasing subsequence is at most `N` equals `Σ_{λ ⊢ n, λ₁ ≤ N} (f^λ)²`.
* `Gessel` (lit, Gessel 1990): **the wall as a Toeplitz determinant**. As formal power series in `x`,
  `Σ_n #{σ ∈ S_n : LIS σ ≤ N} x^{2n}/(n!)² = det (I_{|i−j|}(2x))_{i,j < N}`, with
  `I_k(2x) = Σ_m x^{2m+k}/(m!(m+k)!)`. Equivalently, `P(λ₁ ≤ N)` under (poissonised) Plancherel is a
  `U(N)` Haar average.
* `LoganSheppVershikKerov` (lit): `E[λ₁]/√n → 2`.
* `SoftEdgeLimitExists` (lit, Baik–Deift–Johansson 1999): `λ₁` fluctuates on the scale `n^{1/6}`
  around `2√n`, with a non-degenerate limit law. The limit is the **Tracy–Widom** `F₂`
  (an Airy-kernel Fredholm determinant, equivalently a Painlevé II solution); Mathlib has neither
  the Airy function nor `F₂`, so this statement asserts the existence of the limit law only.

## Hard edge (the moment measure, a wall at `N`)
For `k ≥ 1`, `P_{k,N}(λ) ∝ s_λ(1^k)²` on shapes with at most `k` rows and `λ₁ ≤ N` (the `k × N` box);
`E_{U(N)} |Λ_U(1)|^{2k}` is its normalising sum (RMTlib#19, Loop 3).
* `BumpGamburd` (lit; **computed** for `k ≤ 4`, `N ≤ 40`): `Σ_{λ ⊆ k × N} s_λ(1^k)² = s_{⟨N^k⟩}(1^{2k})`.
* `BoxComplementSymmetry` (**computed**, same range): `P_{k,N}` is invariant under
  `λ_i ↦ N − λ_{k−1−i}` (the functional equation; the wall at `N` mirrors the floor at `0`).
* `HardEdgeWallMass` (**conjecture**, computed to `N = 320` for `k = 2`): `N · P_{k,N}(λ₁ = N) → k²`.
  Reading (not formalised): `λ/N` tends to the `k`-point Legendre ensemble, the wall is its hard
  edge, and `k² = Σ_{j<k} (2j+1)` is the Christoffel–Darboux kernel there (Bessel, not Airy).
-/

namespace RMT.Edges

open Finset Filter Topology
open scoped Nat

/-! ## Shapes and Plancherel measure -/

/-- Partitions of `n`, as weakly decreasing row vectors of length `n`. -/
def shapes (n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => range (n + 1)).filter fun ν => Antitone ν ∧ ∑ i, ν i = n

/-- The top row `λ₁` (zero for the empty shape). -/
def topRow {n : ℕ} (ν : Fin n → ℕ) : ℕ := if h : 0 < n then ν ⟨0, h⟩ else 0

/-- The Plancherel weight `(f^λ)² / n!`. -/
noncomputable def plancherel (n : ℕ) (ν : Fin n → ℕ) : ℝ := (fSYT n ν : ℝ) ^ 2 / (n ! : ℝ)

/-- `P_n(λ₁ ≤ x)` under Plancherel. -/
noncomputable def plancherelTop (n : ℕ) (x : ℝ) : ℝ :=
  ∑ ν ∈ (shapes n).filter (fun ν => (topRow ν : ℝ) ≤ x), plancherel n ν

/-- `E_n[λ₁]` under Plancherel. -/
noncomputable def meanTop (n : ℕ) : ℝ := ∑ ν ∈ shapes n, plancherel n ν * topRow ν

/-- **lit**: the Plancherel weights sum to `1` (`Σ (f^λ)² = n!`). -/
def PlancherelNormalised : Prop := ∀ n, ∑ ν ∈ shapes n, plancherel n ν = 1

/-! ## Longest increasing subsequences -/

/-- `S` is an increasing subsequence of `σ`. -/
def IsIncreasingOn {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i < j → σ i < σ j

open Classical in
/-- The length of a longest increasing subsequence. -/
noncomputable def lis {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((univ : Finset (Finset (Fin n))).filter (IsIncreasingOn σ)).sup card

open Classical in
/-- **lit** (Schensted, via RSK): `#{σ : LIS σ ≤ N} = Σ_{λ ⊢ n, λ₁ ≤ N} (f^λ)²`. -/
def RSKLongestIncreasing : Prop :=
  ∀ n N : ℕ, (((univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => lis σ ≤ N)).card : ℕ) =
    ∑ ν ∈ (shapes n).filter (fun ν => topRow ν ≤ N), (fSYT n ν) ^ 2

/-! ## The wall as a Toeplitz determinant (Gessel) -/

/-- `I_k(2x) = Σ_m x^{2m+k}/(m!(m+k)!)` as a formal power series in `x`. -/
noncomputable def besselI (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun d => if k ≤ d ∧ Even (d - k) then
    1 / ((((d - k) / 2)! : ℚ) * (((d + k) / 2)! : ℚ)) else 0

/-- The Toeplitz matrix `(I_{|i−j|}(2x))_{i,j < N}`. -/
noncomputable def toeplitzBessel (N : ℕ) : Matrix (Fin N) (Fin N) (PowerSeries ℚ) :=
  Matrix.of fun i j => besselI (Int.natAbs ((i : ℤ) - j))

open Classical in
/-- **lit** (Gessel): `det (I_{|i−j|}(2x))_{N×N} = Σ_n #{σ ∈ S_n : LIS σ ≤ N} x^{2n}/(n!)²`. -/
def Gessel : Prop :=
  ∀ N : ℕ, (toeplitzBessel N).det = PowerSeries.mk fun d =>
    if Even d then
      (((univ : Finset (Equiv.Perm (Fin (d / 2)))).filter (fun σ => lis σ ≤ N)).card : ℚ) /
        ((d / 2)! : ℚ) ^ 2
    else 0

/-! ## The soft edge -/

/-- **lit** (Logan–Shepp, Vershik–Kerov): `E[λ₁]/√n → 2`. -/
def LoganSheppVershikKerov : Prop :=
  Tendsto (fun n : ℕ => meanTop n / Real.sqrt n) atTop (𝓝 2)

/-- **lit** (Baik–Deift–Johansson): `(λ₁ − 2√n)/n^{1/6}` has a non-degenerate limit law (the
Tracy–Widom `F₂`, not formalised here). -/
def SoftEdgeLimitExists : Prop :=
  ∃ F : ℝ → ℝ, Monotone F ∧ Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1) ∧
    ∀ s : ℝ, Tendsto (fun n : ℕ => plancherelTop n (2 * Real.sqrt n + s * (n : ℝ) ^ (1 / 6 : ℝ)))
      atTop (𝓝 (F s))

/-! ## The hard edge: the moment measure on the `k × N` box -/

/-- `s_λ(1^k)`, the dimension of the `U(k)` representation of highest weight `λ`. -/
noncomputable def dimU (k : ℕ) (ν : Fin k → ℕ) : ℚ :=
  RMT.Symmetric.schurV (fun _ => (1 : ℚ)) k k ν

/-- Shapes with at most `k` rows and `λ₁ ≤ N`: the `k × N` box. -/
def box (k N : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ => range (N + 1)).filter Antitone

/-- The moment measure `P_{k,N}(λ) = s_λ(1^k)² / Σ_{μ ⊆ k×N} s_μ(1^k)²`. -/
noncomputable def momentMass (k N : ℕ) (ν : Fin k → ℕ) : ℝ :=
  ((dimU k ν : ℝ)) ^ 2 / ∑ μ ∈ box k N, ((dimU k μ : ℝ)) ^ 2

/-- **lit** (Bump–Gamburd; computed for `k ≤ 4`, `N ≤ 40`):
`Σ_{λ ⊆ k×N} s_λ(1^k)² = s_{⟨N^k⟩}(1^{2k})` (`= E_{U(N)} |Λ_U(1)|^{2k}`). -/
def BumpGamburd : Prop :=
  ∀ k N : ℕ, ∑ ν ∈ box k N, (dimU k ν) ^ 2 =
    RMT.Symmetric.schurV (fun _ => (1 : ℚ)) k (2 * k) (fun _ => N)

/-- **computed** (`k ≤ 4`, `N ≤ 40`): the box-complement symmetry
`P_{k,N}(λ) = P_{k,N}(N − λ_{k−1−i})`, the functional equation. -/
def BoxComplementSymmetry : Prop :=
  ∀ k N : ℕ, ∀ ν ∈ box k N, momentMass k N (fun i => N - ν (Fin.rev i)) = momentMass k N ν

/-- **conjecture** (computed to `N = 320` for `k = 2`): the mass at the wall,
`N · P_{k,N}(λ₁ = N) → k²` (a hard edge). -/
def HardEdgeWallMass : Prop :=
  ∀ k : ℕ, 1 ≤ k → Tendsto
    (fun N : ℕ => (N : ℝ) * ∑ ν ∈ (box k N).filter (fun ν => topRow ν = N), momentMass k N ν)
    atTop (𝓝 ((k : ℝ) ^ 2))

end RMT.Edges
