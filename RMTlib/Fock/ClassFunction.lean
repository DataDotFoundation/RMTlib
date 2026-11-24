import RMTlib.Fock.Fischer
import RMTlib.Tableaux.Pieri

/-!
# The Fock pairing on class functions: content-twisted Hall

The Fischer (Fock) pairing on polynomials in the entries of an `N × N` matrix `X` (the RH
formalisation's `fockQ`) restricts, on class functions, to the Hall pairing twisted by the
hook-content product:

  `⟨s_λ(X), s_μ(X)⟩_Fock = δ_{λμ} · ∏_{(i,c) ∈ λ} (N + c − i)`.

This is the precise form of the analogy with the Fock contraction
`Δ = exp (Σ_k k ∂_{p_k} ∂_{p̃_k})` of Dehaye, arXiv:math/0601348, which gives the untwisted Hall
pairing. The twist `∏ (N + c − i) = s_λ(1^N) · H(λ)` tends to `N^{|λ|}` as `N → ∞`. So the Fock
pairing is `N^{deg}` times the Hall pairing only in the large-`N` limit. The general Schur-basis
statement is checked numerically (`scripts/fischer_class_functions.py`: `N = 2`, `|λ| ≤ 4`;
`N = 3`, `|λ| ≤ 3`).

Proved here is the power-sum `p₁^m = (tr X)^m` instance, where both sides are explicit:

* `RMT.Fock.fischer_trX_pow`: `‖(tr X)^m‖²_Fock = m! · N^m`, from the adjointness of `x_v` and
  `∂/∂x_v`.
* `twisted_hall_p1`: `Σ_{λ ⊢ m} (f^λ)² ∏_{(i,c)∈λ} (N + c − i) = m! · N^m`. Here `f^λ` is the
  Schur coefficient of `p₁^m`, and the identity uses the hook-length and hook-content formulas
  and `Σ_λ f^λ s_λ(1^N) = N^m` (`RMT.sum_fSYT_mul_gtCount`, by branching and Pieri).
* `fischer_trX_pow_eq_twisted_hall`: the two agree.

For every shape, `RMTlib.Fock.Laplacian` proves that the Fock adjoint of `tr X` removes one box
with weight `N + c` (`RMT.Fock.trD_sX`), hence `⟨(tr X)^m, s_λ(X)⟩_Fock = f^λ ∏ (N + c − i)`
(`RMT.Fock.fischer_trX_pow_sX`). `RMTlib.Fock.Orthogonality` proves `⟨h_k(X), e_k(X)⟩ = 0` for
`k ≥ 2`. The general diagonal remains open (`bridge/links/fock-norm.md`, §3).
-/

open Finset
open scoped Nat

namespace RMT

/-- The content-twisted Hall norm of `p₁^m = Σ_λ f^λ s_λ`. -/
theorem twisted_hall_p1 (N m : ℕ) :
    ∑ ν ∈ parts N m, (fSYT m ν : ℚ) ^ 2 * ∏ i : Fin N, ∏ c ∈ range (ν i), ((N - i + c : ℕ) : ℚ) =
      (m ! : ℚ) * (N : ℚ) ^ m := by
  rw [← sum_fSYT_mul_gtCount m, mul_sum]
  refine sum_congr rfl fun ν hν => ?_
  obtain ⟨hanti, hs⟩ := mem_parts.mp hν
  have hHL := hook_length_formula ν hanti
  have hHC := hook_content_formula N ν hanti
  rw [hs] at hHL
  have hHL' : (fSYT m ν : ℚ) * hookProd ν = m ! := by exact_mod_cast hHL
  have hHC' : (gtCount N ν : ℚ) * hookProd ν = ∏ i : Fin N, ∏ c ∈ range (ν i), ((N - i + c : ℕ) : ℚ) := by
    exact_mod_cast hHC
  rw [← hHC', ← hHL']
  ring

/-- **The Fock pairing on `(tr X)^m` is the content-twisted Hall pairing** of `p₁^m`. -/
theorem fischer_trX_pow_eq_twisted_hall (N m : ℕ) :
    Fock.fischer (Fock.trX N ^ m) (Fock.trX N ^ m) =
      ∑ ν ∈ parts N m, (fSYT m ν : ℚ) ^ 2 * ∏ i : Fin N, ∏ c ∈ range (ν i), ((N - i + c : ℕ) : ℚ) := by
  rw [Fock.fischer_trX_pow, twisted_hall_p1]

end RMT
