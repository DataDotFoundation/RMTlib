import RMTlib.RSK.GrowthGeneric

/-!
# The null chart: exchanging the two axes of a growth diagram (#154, target 2a)

In the owner's null chart (RMTlib#142, #154), a growth diagram is a discrete Goursat problem on
`ℙ¹ × ℙ¹`: the two outer edges (the null boundary lines) determine the interior
(`RMT.RSK.GrowthGeneric.eq_of_edges`, `back_grow`). `Sym² ℙ¹` is the quotient by exchanging the
two null axes. This file proves the axis exchange is a symmetry of RSK's growth diagram:

* `pmax_comm`, `fwd_comm`: Fomin's local rule is symmetric in its two neighbours;
* `grow_transpose`: **the grid of `σᵀ` (`σ ↦ σ⁻¹`) is the grid of `σ` with the axes exchanged**;
* `grow_transpose_edges`: the two edges are exchanged (`P ↔ Q`) and the corner shape is kept.

The other involution, reflecting one axis (reversing `σ`), transposes the shape: that is ω
(Schensted), not this exchange (MeaningLib's computation on all permutations with `n ≤ 7`). It is
#154 target 2b.
-/

namespace RMT.RSK.Growth

theorem pmax_comm : ∀ l m : Part, pmax l m = pmax m l
  | a :: l, b :: m => by simp [pmax, Nat.max_comm, pmax_comm l m]
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

/-- **The local rule is symmetric in its two neighbours.** -/
theorem fwd_comm (ρ μ ν : Part) (x : Bool) : fwd ρ μ ν x = fwd ρ ν μ x := by
  unfold fwd
  by_cases h : μ = ν
  · subst h; rfl
  · rw [ite_eq_left h, ite_eq_left (Ne.symm h), pmax_comm]

/-- **Exchanging the two null axes transposes the grid**: the growth diagram of `σᵀ` (`σ ↦ σ⁻¹`)
is the growth diagram of `σ` with its two coordinates exchanged. -/
theorem grow_transpose (σ : Nat → Nat → Bool) (N : Nat) :
    ∀ i j, grow (fun a b => σ b a) N i j = grow σ N j i
  | 0, j => by cases j <;> simp [grow]
  | i + 1, 0 => by simp [grow]
  | i + 1, j + 1 => by
    rw [grow_succ, grow_succ, grow_transpose σ N i j, grow_transpose σ N (i + 1) j,
      grow_transpose σ N i (j + 1), fwd_comm]
termination_by i j => i + j

/-- **The two edges are exchanged** (`P ↔ Q`), and the shape at the corner is unchanged. -/
theorem grow_transpose_edges (σ : Nat → Nat → Bool) (N n m : Nat) :
    (∀ j, grow (fun a b => σ b a) N n j = grow σ N j n) ∧
      grow (fun a b => σ b a) N n m = grow σ N m n :=
  ⟨fun j => grow_transpose σ N n j, grow_transpose σ N n m⟩

end RMT.RSK.Growth
