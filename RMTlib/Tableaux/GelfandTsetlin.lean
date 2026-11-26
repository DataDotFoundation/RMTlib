import RMTlib.Tableaux.Interlaced

/-!
# The RH formalisation's index set is made of Gelfand–Tsetlin patterns

`RMT.Weyl.Interlaced m` (the RH formalisation's `Interlaced`, which indexes its basis of the dual
Weyl module) says: for every `a`, the shape formed by the entries `≤ a` of the filling of `m`
interlaces, in the Gelfand–Tsetlin sense, into the shape formed by the entries `≤ a + 1`
(`interlaced_iff_gt`). So the index set is the set of Gelfand–Tsetlin patterns, i.e. chains of
branching steps `U(k) ⊃ U(k−1) ⊃ ⋯ ⊃ U(1)`. Each step is the branching condition that, after
the `ρ`-shift, is the archimedean Gan–Gross–Prasad interlacing condition of the RH formalisation
(`PI.BesselPeriodGGP.InterlacingCondition`; see `RMT.Bridge.ggp_interlacing_iff` in the bridge
package).
-/

open Finset

namespace RMT.Weyl

variable {k n : ℕ}

/-- The shape formed by the entries `< a` (i.e. `≤ a` in 1-based labels): row `t` has
`Σ_{b<a} m(b, t)` boxes. -/
def prefixShape (m : Fin k × Fin n → ℕ) (a : ℕ) : Fin n → ℕ :=
  fun t => ∑ b : Fin k with b.val < a, m (b, t)

/-- `μ` interlaces into `λ` (Gelfand–Tsetlin branching): `λ_{t+1} ≤ μ_t ≤ λ_t`. -/
def GTStep (lam mu : Fin n → ℕ) : Prop :=
  (∀ l j : Fin n, j.val = l.val + 1 → lam j ≤ mu l) ∧ ∀ t, mu t ≤ lam t

theorem prefixShape_mono (m : Fin k × Fin n → ℕ) (a : ℕ) (t : Fin n) :
    prefixShape m a t ≤ prefixShape m (a + 1) t :=
  sum_le_sum_of_subset_of_nonneg
    (by intro b hb; simp only [mem_filter, mem_univ, true_and] at hb ⊢; omega)
    (fun _ _ _ => Nat.zero_le _)

/-- **`Interlaced` is the Gelfand–Tsetlin condition**: every consecutive pair of prefix shapes
is a branching step. -/
theorem interlaced_iff_gt (m : Fin k × Fin n → ℕ) :
    Interlaced m ↔ ∀ a : Fin k, GTStep (prefixShape m (a.val + 1)) (prefixShape m a.val) := by
  have hle : ∀ (a b : Fin k), (b ≤ a ↔ b.val < a.val + 1) := fun a b => by
    rw [Fin.le_def]; omega
  have hlt : ∀ (a b : Fin k), (b < a ↔ b.val < a.val) := fun a b => Fin.lt_def
  constructor
  · intro h a
    refine ⟨fun l j hj => ?_, fun t => prefixShape_mono m _ t⟩
    have := h l j hj a
    simp only [prefixShape]
    convert this using 2
    · ext b; simp only [mem_filter, mem_univ, true_and, hle a b]
  · intro h l j hj a
    have := (h a).1 l j hj
    simp only [prefixShape] at this
    convert this using 2
    · ext b; simp only [mem_filter, mem_univ, true_and, hle a b]

end RMT.Weyl
