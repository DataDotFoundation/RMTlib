import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import MeaningLib.Frame.Pattern

/-!
# The second Adams operation on eigenvalues: `ψ² = Sym² − ∧²`

For the eigenvalues `s` of a representation `ρ` (a multiset in a commutative ring):

* `tr (ρ ⊗ ρ) = (Σ s)²`, `tr (∧² ρ) = e₂(s)`, `tr (Sym² ρ) = h₂(s) = (Σ s)² − e₂(s)`;
* `tr (ψ² ρ) = p₂(s) = Σ s_i²`.

`sum_sq_eq` (Newton in degree 2, on multisets): `p₂ = (Σ s)² − 2 e₂`, i.e. `ψ² = ρ ⊗ ρ − 2 ∧² ρ`
and `ψ² = Sym² ρ − ∧² ρ`; in plethystic notation `p₂ = h₂ − e₂` and `h₁² = h₂ + e₂`. RH-Dual#20
found this, unnamed, in Alpöge's proof (`GoodMetric.PureVirt.ptr_tensor_sub_wedge2`); the statements
here are tagged `@[frame_pattern]` so a checker can match it.

**ω.** `ω` exchanges `h₂` and `e₂` (`Sym² ↔ ∧²`), so `ω p₂ = −p₂`: `ψ²` is `ω`-anti-covariant.
The bosonic `h₂ = (Σ s)² − e₂` and the fermionic `e₂` differ by the sign of the `e₂` term.
-/

namespace RMT.Plethysm

variable {R : Type*} [CommRing R]

/-- `h₂` of a multiset, the trace of `Sym²`: `(Σ s)² − e₂(s)`. Defined by this formula; see
`hTwo_eq` for the sum over pairs `i ≤ j`. -/
def hTwo (s : Multiset R) : R := s.sum ^ 2 - s.esymm 2

theorem esymm_two_cons (a : R) (s : Multiset R) :
    (a ::ₘ s).esymm 2 = a * s.sum + s.esymm 2 := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one,
    Multiset.map_add, Multiset.map_map, Multiset.sum_add, Function.comp_def, Multiset.prod_cons,
    Multiset.prod_singleton, add_comm]
  rw [Multiset.sum_map_mul_left, Multiset.map_id']

/-- **Newton in degree 2** (`ψ² = ρ ⊗ ρ − 2 ∧² ρ`): `Σ s_i² = (Σ s)² − 2 e₂(s)`. -/
@[frame_pattern]
theorem sum_sq_eq (s : Multiset R) : (s.map (· ^ 2)).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, esymm_two_cons]
    ring

/-- **`ψ² = Sym² − ∧²`** (`p₂ = h₂ − e₂`). -/
@[frame_pattern]
theorem sum_sq_eq_hTwo_sub (s : Multiset R) : (s.map (· ^ 2)).sum = hTwo s - s.esymm 2 := by
  rw [sum_sq_eq, hTwo]
  ring

/-- **`ρ ⊗ ρ = Sym² + ∧²`** (`h₁² = h₂ + e₂`). -/
@[frame_pattern]
theorem sum_sq_eq_hTwo_add (s : Multiset R) : s.sum ^ 2 = hTwo s + s.esymm 2 := by
  rw [hTwo]
  ring

end RMT.Plethysm
