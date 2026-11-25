import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# One-body weights on Maya sites: affine potential or not

In the place-uniform form of Bump–Diaconis / Tracy–Widom (RMTlib#21, pattern A of RMTlib#19), a
place `v` enters only through a one-body weight `ρ_v : ℕ → R` on Maya sites:
`ρ_p(l) = T^l` at a finite place and `ρ_∞(l) = l!` at `∞`. The bosonic (skew-Cauchy) form of the
identity (pattern B) needs the potential `φ = log ρ` to be **affine** in the site, i.e. `ρ`
exponential-linear (`IsExpLinear`). That hypothesis is the single root of the four violations
mapped in RMTlib#21: content dependence and operator order are "`φ` not affine", the wall is its
zero set, the zero radius its growth.

* `isExpLinear_pow`: the finite place satisfies it.
* `not_isExpLinear_factorial`: `∞` does not, in any nontrivial ring (`0! = 1`, `1! = 1`, `2! = 2`
  force `1 = 2`). So when pattern B is matched at `∞`, the open side goal `IsExpLinear ρ_∞` comes
  with a proof that it is false: the violation is located and certified.
-/

namespace RMT.BDTW

variable {R : Type*} [CommRing R]

/-- **An affine one-body potential**: `ρ l = c · T^l` (`φ = log ρ` affine in the site `l`). -/
def IsExpLinear (ρ : ℕ → R) : Prop := ∃ c T : R, ∀ l, ρ l = c * T ^ l

/-- The finite place: `ρ_p(l) = T^l` is exponential-linear. -/
theorem isExpLinear_pow (T : R) : IsExpLinear (fun l => T ^ l) := ⟨1, T, fun l => by simp⟩

/-- **`∞` violates it**: `l ↦ l!` is not exponential-linear in any nontrivial ring. -/
theorem not_isExpLinear_factorial [Nontrivial R] : ¬ IsExpLinear (fun l => (l.factorial : R)) := by
  rintro ⟨c, T, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [Nat.factorial, Nat.cast_one, pow_zero, mul_one, pow_one, Nat.succ_eq_add_one,
    zero_add] at h0 h1 h2
  rw [← h0, one_mul] at h1
  rw [← h0, ← h1, one_pow, one_mul] at h2
  have : (1 : R) = 0 := by linear_combination h2
  exact one_ne_zero this

end RMT.BDTW
