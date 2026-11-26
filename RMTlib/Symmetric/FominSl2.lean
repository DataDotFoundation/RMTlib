import RMTlib.Symmetric.FominMaya
import RMTlib.Symmetric.CornerWeighted

/-!
# Weighted up and down operators: the commutator, `sl₂`, and points of `ℙ¹`

Fomin's operators with a weight on each side: `U_u` adds a box of content `c` with weight `u(c)`
(`upW`), `D_d` removes one with weight `d(c)` (`down`). Think of the content line `ℤ` inside
`ℙ¹ = ℤ ∪ {∞}`; an affine weight `c ↦ z + c` is a section of `O(1)`, determined by its zero `−z`
(the constant weight `1` vanishes at `∞`).

The weighted commutator is `RMT.Symmetric.Corners.commutator_weighted_single`
(`RMTlib.Symmetric.CornerWeighted`): `[D_d, U_u]` is diagonal and only the product `u·d` matters;
there the `sl₂` relation is proved off the full shapes (`sl2_commutator`). This file adds the Maya
reading and the full shapes.

* `commutator_weighted_maya`: on the Maya diagram, the eigenvalue is the gradient of `ud` over the
  particles plus `(ud)(−N)` when the wall site is occupied.
* `sl2_commutator_all` (**`sl₂` on every shape**): for `u = z + c`, `d = z' + c`,
  `[D, U] e_ν = (2|ν| + z z') e_ν` off the full shapes, and `− (z − N)(z' − N)` more on them:
  `[L₁, L₋₁] = 2 L₀` with `L₀ = |ν| + z z'/2`, the relation behind Okounkov's `SL(2)` construction of
  the `z`-measures. Off the wall, the commutator depends on the two points `−z, −z'` of `ℙ¹` only
  through `z z'`.
* `sl2_commutator_wall`: **a truncation is a zero at the wall**. If `d` vanishes at the wall point
  `−N` (`z' = N`), the wall term vanishes and `[D, U] = 2|ν| + z N` on every shape with at most `N`
  rows, full or not.

With `u = 1` (the zero of `u` at `∞`) the commutator is Fomin's `[D_r, U]` of
`RMTlib.Symmetric.FominMaya`; with `d = N + c` it is the `U(N)` weight of `L₁` at charge `N`
(`RMT.Fock.Virasoro.L1_eDetP`).
-/

open Finset

noncomputable section

namespace RMT.Symmetric.Corners

variable {N : ℕ} {R : Type*} [CommRing R]

/-- **The weighted commutator on the Maya diagram**: `[D_d, U_u] e_ν` is
`(Σ_{particles x} ((ud)(x+1) − (ud)(x)) + [−N occupied] (ud)(−N)) e_ν`. -/
theorem commutator_weighted_maya {ν : Fin N → ℕ} (hν : Antitone ν) (u d : ℤ → R) :
    down N d (upW N u (Finsupp.single ν 1)) - upW N u (down N d (Finsupp.single ν 1)) =
      ((∑ x ∈ mayaSet ν, (u (x + 1) * d (x + 1) - u x * d x)) +
        if -(N : ℤ) ∈ mayaSet ν then u (-(N : ℤ)) * d (-(N : ℤ)) else 0) •
        Finsupp.single ν 1 := by
  rw [commutator_weighted_single hν d u, sum_corners_eq_maya hν (fun c => d c * u c)]
  congr 2
  · refine sum_congr rfl fun x _ => ?_; ring
  · split_ifs <;> ring

theorem sum_fin_cast (N : ℕ) : ∑ i : Fin N, ((i : ℕ) : R) * 2 = (N : R) * N - N := by
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun i => (i : R)) N]
  have h := Finset.sum_range_id_mul_two N
  rcases N with _ | n
  · simp
  · rw [Nat.add_sub_cancel] at h
    have := congrArg (Nat.cast : ℕ → R) h
    push_cast at this ⊢
    linear_combination this

/-- **The `sl₂` relation** (Okounkov's `z`-measures, read on Fomin's operators): with
`U` adding a box with weight `z + c` and `D` removing one with weight `z' + c`,
`[D, U] e_ν = (2|ν| + z z') e_ν` off the full shapes, and `2|ν| + z z' − (z − N)(z' − N)` on them.
So `[D, U] = 2 L₀` with `L₀ = |ν| + z z'/2`, up to the wall. The weights are sections of `O(1)`
on `ℙ¹ = ℤ ∪ {∞}` vanishing at `−z` and `−z'`. -/
theorem sl2_commutator_all {ν : Fin N → ℕ} (hν : Antitone ν) (z z' : R) :
    down N (fun c => z' + c) (upW N (fun c => z + c) (Finsupp.single ν 1)) -
        upW N (fun c => z + c) (down N (fun c => z' + c) (Finsupp.single ν 1)) =
      (2 * ((∑ i, ν i : ℕ) : R) + z * z' -
        if Full ν then (z - N) * (z' - N) else 0) • Finsupp.single ν 1 := by
  rw [commutator_weighted_maya hν]
  congr 1
  have hinj : Set.InjOn (maya ν) (univ : Finset (Fin N)) := fun i _ j _ h => maya_injective hν h
  have hS : ∑ x ∈ mayaSet ν, ((z + ((x + 1 : ℤ) : R)) * (z' + ((x + 1 : ℤ) : R)) -
      (z + (x : R)) * (z' + (x : R))) =
      2 * ((∑ i, ν i : ℕ) : R) + N * (z + z') - N * N := by
    rw [mayaSet, sum_image hinj]
    have e : ∀ i : Fin N, (z + ((maya ν i + 1 : ℤ) : R)) * (z' + ((maya ν i + 1 : ℤ) : R)) -
        (z + ((maya ν i : ℤ) : R)) * (z' + ((maya ν i : ℤ) : R)) =
        (z + z' - 1) + 2 * (ν i : R) - ((i : ℕ) : R) * 2 := fun i => by
      unfold maya; push_cast; ring
    simp_rw [e]
    rw [sum_sub_distrib, sum_fin_cast, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      ← mul_sum]
    push_cast; ring
  rw [hS]
  by_cases hf : Full ν
  · rw [ite_eq_right (by rw [neg_mem_mayaSet_iff hν]; exact not_not.mpr hf), ite_eq_left hf]
    push_cast; ring
  · rw [ite_eq_left ((neg_mem_mayaSet_iff hν).mpr hf), ite_eq_right hf]
    push_cast; ring

/-- **A truncation is a zero of the weight at the wall**: if `D` removes with weight `N + c`,
which vanishes at the wall point `−N`, the relation `[D, U] = 2|ν| + z N` holds on every shape
with at most `N` rows, full or not. -/
theorem sl2_commutator_wall {ν : Fin N → ℕ} (hν : Antitone ν) (z : R) :
    down N (fun c => (N : R) + c) (upW N (fun c => z + c) (Finsupp.single ν 1)) -
        upW N (fun c => z + c) (down N (fun c => (N : R) + c) (Finsupp.single ν 1)) =
      (2 * ((∑ i, ν i : ℕ) : R) + z * N) • Finsupp.single ν 1 := by
  rw [sl2_commutator_all hν]
  congr 1
  split_ifs <;> ring

end RMT.Symmetric.Corners
