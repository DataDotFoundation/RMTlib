import RMTlib.Symmetric.CornerMoments

/-!
# Fomin's up/down operators on the Maya diagram

`RMTlib.Symmetric.CornerMoments` proves Fomin's relation `[D_r, U] = r(0)` for the up and down
operators on partitions with at most `N` rows (`U` adds a box with weight `1`, `D_r` removes a box
`□` with weight `r(c(□))`), for affine `r`, off the full shapes. This file reads the same operators
on the Maya diagram, `ν ↦ {b_i = ν_i − i − 1}` (`mayaSet`), where they become **particle hops**,
and computes the commutator there for **every** weight `r`.

## The dictionary

* `isAddable_iff_maya`: row `i` is addable iff the site `b_i + 1` is empty (the particle can hop
  right); the added box has content `b_i + 1`.
* `isCorner_iff_maya`: row `i` is removable iff the site `b_i − 1` is empty and `b_i > −N` (the
  particle can hop left without crossing the wall at `−N`); the removed box has content `b_i`.
* `mayaSet_addBox`, `mayaSet_removeBox`: the new Maya set is the old one with one particle moved.
* `upHop`, `downHop`: the hop operators on finitely supported functions of Maya sets
  (`U = Σ_x c†_{x+1} c_x`, `D_r = Σ_x r(x) c†_{x−1} c_x` above a wall `L`; a hop between adjacent
  sites passes no other particle, so there are no fermionic signs).
* `mapDomain_up`, `mapDomain_down`: **`mayaSet` intertwines `U` and `D_r` on partitions with the
  hops**, with the wall at `−N`.

## The commutator on fermions

* `sum_hops`: right-hop weights minus left-hop weights telescope to the discrete gradient of `r`
  over the particles, plus `r(L)` if the wall site is occupied.
* `commutator_single_maya`, `hop_commutator`: **`[D_r, U] e_S = (Σ_{x ∈ S} (r(x+1) − r(x)) +
  [−N ∈ S] r(−N)) e_S`** for every `r`: the commutator is diagonal, the total gradient of `r` over
  the particles plus a wall term.
* `hop_commutator_grad`, `neg_mem_mayaSet_iff`: **Fomin's relation is a constant gradient.** If
  `r(x+1) − r(x) = a` the eigenvalue is `a · N` plus `r(−N)` when the wall site is occupied, which
  happens exactly off the full shapes. For affine `r` this is `r(0)` off the full shapes and
  `r(0) − r(−N)` on them (`commutator_single_affine`), and the converse direction
  (`commutator_eq_iff_affine`) reads: the commutator depends on the shape only through `N` and the
  wall exactly when the gradient is constant.

## ω, in a box

In the window `[L, M − 1]` (partitions in an `N × M` box when `L = −N`), let `fominEigen` be the
gradient over the particles plus the bottom wall term minus the top wall term, the eigenvalue of
the commutator with walls at both ends. `ω` sends the Maya set to its holes reflected by
`y ↦ −1 − y` (`conjBox`, the transposed shape in the window `[−M, −L − 1]`). Then
`fominEigen_conjBox`: **the eigenvalue of `S` for `r` is that of `ωS` for `r(−·)`**: `ω` exchanges
particles and holes and the two walls, and reflects the contents.
-/

open Finset

namespace RMT.Symmetric.Corners

variable {N : ℕ}

theorem mem_mayaSet {ν : Fin N → ℕ} {x : ℤ} : x ∈ mayaSet ν ↔ ∃ i, maya ν i = x := by
  simp [mayaSet]

/-- **Adding a box is a particle hopping right**: row `i` is addable iff the site `b_i + 1` to the
right of its particle is empty. -/
theorem isAddable_iff_maya {ν : Fin N → ℕ} (hν : Antitone ν) (i : Fin N) :
    RMT.IsAddable ν i = true ↔ maya ν i + 1 ∉ mayaSet ν := by
  rw [mem_mayaSet, not_exists]
  unfold RMT.IsAddable maya
  constructor
  · intro h j hj
    by_cases hji : j < i
    · have hi : 0 < i.val := by have : j.val < i.val := hji; omega
      rw [dite_eq_left hi] at h
      have h1 := hν (show j ≤ ⟨i.val - 1, by omega⟩ by rw [Fin.le_def]; simp; omega)
      simp at h
      have : j.val < i.val := hji
      omega
    · have h1 := hν (show i ≤ j by simpa using hji)
      have : i.val ≤ j.val := by simpa using hji
      omega
  · intro h
    split_ifs with hi
    · by_contra hc
      have h1 := hν (show (⟨i.val - 1, by omega⟩ : Fin N) ≤ i by rw [Fin.le_def]; simp)
      simp at hc
      exact h ⟨i.val - 1, by omega⟩ (by simp; omega)
    · rfl

/-- **Removing a box is a particle hopping left**: row `i` is removable iff the site `b_i − 1` is
empty and the particle is not at the wall `−N`. -/
theorem isCorner_iff_maya {ν : Fin N → ℕ} (hν : Antitone ν) (i : Fin N) :
    RMT.IsCorner ν i = true ↔ maya ν i - 1 ∉ mayaSet ν ∧ -(N : ℤ) < maya ν i := by
  rw [mem_mayaSet, not_exists]
  unfold RMT.IsCorner maya
  have hiN := i.isLt
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h0, h1⟩ := h
    refine ⟨fun j hj => ?_, by omega⟩
    by_cases hij : i < j
    · have hn : i.val + 1 < N := by have : i.val < j.val := hij; omega
      rw [dite_eq_left hn] at h1
      have h2 := hν (show (⟨i.val + 1, hn⟩ : Fin N) ≤ j by rw [Fin.le_def]; simp; exact hij)
      simp at h1
      have : i.val < j.val := hij
      omega
    · have h2 := hν (show j ≤ i by simpa using hij)
      have : j.val ≤ i.val := by simpa using hij
      omega
  · rintro ⟨h, hw⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    by_cases hn : i.val + 1 < N
    · rw [dite_eq_left hn]
      have h2 := hν (show i ≤ (⟨i.val + 1, hn⟩ : Fin N) by rw [Fin.le_def]; simp)
      have h3 := h ⟨i.val + 1, hn⟩
      simp at h3
      refine ⟨by omega, ?_⟩
      simp only [decide_eq_true_eq]; omega
    · rw [dite_eq_right hn]; simp; omega

/-! ## The commutator as a sum over particles -/

section Commutator

variable {R : Type*} [CommRing R]

/-- **Hops telescope**: for a finite set of particles `S` above a wall `L`, the weights `r(x+1)`
of the right hops minus the weights `r(x)` of the left hops (not across the wall) are the
discrete gradient of `r` summed over the particles, plus `r(L)` if the wall site is occupied. -/
theorem sum_hops (S : Finset ℤ) {L : ℤ} (hS : ∀ x ∈ S, L ≤ x) (r : ℤ → R) :
    (∑ x ∈ S with x + 1 ∉ S, r (x + 1)) - ∑ x ∈ S with x - 1 ∉ S ∧ L < x, r x =
      ∑ x ∈ S, (r (x + 1) - r x) + if L ∈ S then r L else 0 := by
  have A := sum_filter_add_sum_filter_not S (fun x => x + 1 ∉ S) (fun x => r (x + 1))
  have B := sum_filter_add_sum_filter_not S (fun x => x - 1 ∉ S) r
  have C : ∑ x ∈ S with ¬(x + 1 ∉ S), r (x + 1) = ∑ x ∈ S with ¬(x - 1 ∉ S), r x := by
    refine sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_ <;> simp <;> intro a h1 h2 <;> exact ⟨h2, h1⟩
  have D := sum_filter_add_sum_filter_not (S.filter fun x => x - 1 ∉ S) (fun x => L < x) r
  have E : ∑ x ∈ (S.filter fun x => x - 1 ∉ S) with ¬L < x, r x = if L ∈ S then r L else 0 := by
    have : ((S.filter fun x => x - 1 ∉ S).filter fun x => ¬L < x) =
        if L ∈ S then {L} else ∅ := by
      ext x
      simp only [mem_filter, not_lt]
      split_ifs with hL
      · simp only [mem_singleton]
        constructor
        · rintro ⟨⟨hx, -⟩, hx'⟩; exact le_antisymm hx' (hS x hx)
        · rintro rfl; exact ⟨⟨hL, fun h => by have := hS _ h; omega⟩, le_rfl⟩
      · simp only [notMem_empty, iff_false]
        rintro ⟨⟨hx, -⟩, hx'⟩; exact hL (le_antisymm hx' (hS x hx) ▸ hx)
    rw [this]; split_ifs <;> simp
  rw [filter_filter] at D
  rw [sum_sub_distrib]
  linear_combination A - B - C - D + E

/-- **Fomin's commutator on the Maya diagram, for every weight `r`**:
`[D_r, U] e_ν = (Σ_{particles x} (r(x+1) − r(x)) + [−N occupied] r(−N)) e_ν`.
The commutator is the discrete gradient of `r` summed over the particles, plus a wall term. -/
theorem commutator_single_maya {ν : Fin N → ℕ} (hν : Antitone ν) (r : ℤ → R) :
    down N r (up N R (Finsupp.single ν 1)) - up N R (down N r (Finsupp.single ν 1)) =
      ((∑ x ∈ mayaSet ν, (r (x + 1) - r x)) +
        if -(N : ℤ) ∈ mayaSet ν then r (-(N : ℤ)) else 0) • Finsupp.single ν 1 := by
  rw [commutator_single hν]
  congr 1
  have hwall : ∀ x ∈ mayaSet ν, -(N : ℤ) ≤ x := by
    intro x hx; obtain ⟨i, rfl⟩ := mem_mayaSet.mp hx; unfold maya; have := i.isLt; omega
  rw [← sum_hops (mayaSet ν) hwall r, sum_filter, sum_filter]
  have hinj : Set.InjOn (maya ν) (univ : Finset (Fin N)) := fun i _ j _ h => maya_injective hν h
  conv_rhs => rw [mayaSet, sum_image hinj, sum_image hinj]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    have e := isAddable_iff_maya hν i
    have hv : (ν i : ℤ) - i = maya ν i + 1 := by unfold maya; ring
    by_cases h : RMT.IsAddable ν i = true
    · have h' := e.mp h; unfold mayaSet at h'; simp [h, h', hv]
    · have h' : ¬ maya ν i + 1 ∉ mayaSet ν := fun h' => h (e.mpr h')
      unfold mayaSet at h'; simp only [h, h', Bool.false_eq_true, ite_false]
  · refine sum_congr rfl fun i _ => ?_
    have e := isCorner_iff_maya hν i
    have hv : (ν i : ℤ) - 1 - i = maya ν i := by unfold maya; ring
    by_cases h : RMT.IsCorner ν i = true
    · have h' := e.mp h; unfold mayaSet at h'; simp [h, h', hv]
    · have h' : ¬ (maya ν i - 1 ∉ mayaSet ν ∧ -(N : ℤ) < maya ν i) := fun h' => h (e.mpr h')
      unfold mayaSet at h'; simp only [h, h', Bool.false_eq_true, ite_false]

/-! ## The hop operators on Maya sets, and the dictionary -/

/-- Moving the particle at `x` to `y`. -/
def hop (S : Finset ℤ) (x y : ℤ) : Finset ℤ := insert y (S.erase x)

theorem maya_update (ν : Fin N → ℕ) (i : Fin N) (n : ℕ) (j : Fin N) :
    maya (Function.update ν i n) j = if j = i then (n : ℤ) - i - 1 else maya ν j := by
  unfold maya; split_ifs with h
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- **Changing one row moves one particle.** -/
theorem mayaSet_update {ν : Fin N → ℕ} (hinj : Function.Injective (maya ν)) (i : Fin N) (n : ℕ) :
    mayaSet (Function.update ν i n) = hop (mayaSet ν) (maya ν i) ((n : ℤ) - i - 1) := by
  ext x
  simp only [mem_mayaSet, hop, mem_insert, mem_erase, maya_update]
  constructor
  · rintro ⟨j, hj⟩
    split_ifs at hj with h
    · exact Or.inl hj.symm
    · exact Or.inr ⟨fun hx => h (hinj (hx ▸ hj)), j, hj⟩
  · rintro (rfl | ⟨hx, j, rfl⟩)
    · exact ⟨i, by simp⟩
    · refine ⟨j, ?_⟩
      have hji : j ≠ i := fun h => hx (by rw [h])
      rw [ite_eq_right hji]

theorem mayaSet_addBox {ν : Fin N → ℕ} (hν : Antitone ν) (i : Fin N) :
    mayaSet (RMT.addBox ν i) = hop (mayaSet ν) (maya ν i) (maya ν i + 1) := by
  rw [RMT.addBox, mayaSet_update (maya_injective hν)]; congr 1; unfold maya; push_cast; ring

theorem mayaSet_removeBox {ν : Fin N → ℕ} (hν : Antitone ν) (i : Fin N) (h : 0 < ν i) :
    mayaSet (RMT.removeBox ν i) = hop (mayaSet ν) (maya ν i) (maya ν i - 1) := by
  rw [RMT.removeBox, mayaSet_update (maya_injective hν)]; congr 1; unfold maya; push_cast [h]; ring

/-- `U` on Maya sets: every particle with an empty site to its right hops there. -/
noncomputable def upHopVec (S : Finset ℤ) : Finset ℤ →₀ R :=
  ∑ x ∈ S with x + 1 ∉ S, Finsupp.single (hop S x (x + 1)) 1

/-- `D_r` on Maya sets with a wall at `L`: every particle above the wall with an empty site to its
left hops there, with weight `r(x)` (the content of the removed box). -/
noncomputable def downHopVec (L : ℤ) (r : ℤ → R) (S : Finset ℤ) : Finset ℤ →₀ R :=
  ∑ x ∈ S with x - 1 ∉ S ∧ L < x, Finsupp.single (hop S x (x - 1)) (r x)

variable (R) in
/-- **The up operator on Maya sets** (fermion hops to the right). -/
noncomputable def upHop : (Finset ℤ →₀ R) →ₗ[R] (Finset ℤ →₀ R) := Finsupp.linearCombination R upHopVec

/-- **The down operator on Maya sets**, with a wall at `L`. -/
noncomputable def downHop (L : ℤ) (r : ℤ → R) : (Finset ℤ →₀ R) →ₗ[R] (Finset ℤ →₀ R) :=
  Finsupp.linearCombination R (downHopVec L r)

/-- **`U` on partitions is `U` on Maya sets**: `mayaSet` carries `U e_ν` to the hops of `mayaSet ν`. -/
theorem mapDomain_upVec {ν : Fin N → ℕ} (hν : Antitone ν) :
    Finsupp.mapDomain mayaSet (upVec (R := R) ν) = upHopVec (mayaSet ν) := by
  have hinj : Set.InjOn (maya ν) (univ : Finset (Fin N)) := fun i _ j _ h => maya_injective hν h
  rw [upVec, Finsupp.mapDomain_finsetSum, upHopVec, sum_filter]
  conv_rhs => rw [mayaSet]
  rw [sum_image hinj]
  refine sum_congr rfl fun i _ => ?_
  have e := isAddable_iff_maya hν i
  by_cases h : RMT.IsAddable ν i = true
  · have h' := e.mp h; unfold mayaSet at h'
    simp only [h, ite_true, Finsupp.mapDomain_single, mayaSet_addBox hν, h', not_false_eq_true]
    rfl
  · have h' : ¬ maya ν i + 1 ∉ mayaSet ν := fun h' => h (e.mpr h')
    unfold mayaSet at h'; simp only [h, h', Bool.false_eq_true, ite_false, Finsupp.mapDomain_zero]

/-- **`D_r` on partitions is `D_r` on Maya sets, with the wall at `−N`.** -/
theorem mapDomain_downVec {ν : Fin N → ℕ} (hν : Antitone ν) (r : ℤ → R) :
    Finsupp.mapDomain mayaSet (downVec r ν) = downHopVec (-(N : ℤ)) r (mayaSet ν) := by
  have hinj : Set.InjOn (maya ν) (univ : Finset (Fin N)) := fun i _ j _ h => maya_injective hν h
  rw [downVec, Finsupp.mapDomain_finsetSum, downHopVec, sum_filter]
  conv_rhs => rw [mayaSet]
  rw [sum_image hinj]
  refine sum_congr rfl fun i _ => ?_
  have e := isCorner_iff_maya hν i
  have hv : (ν i : ℤ) - 1 - i = maya ν i := by unfold maya; ring
  by_cases h : RMT.IsCorner ν i = true
  · have h' := e.mp h; unfold mayaSet at h'
    have h0 : 0 < ν i := by unfold RMT.IsCorner at h; simp at h; exact h.1
    simp only [h, ite_true, Finsupp.mapDomain_single, mayaSet_removeBox hν i h0, h', hv]
    rfl
  · have h' : ¬ (maya ν i - 1 ∉ mayaSet ν ∧ -(N : ℤ) < maya ν i) := fun h' => h (e.mpr h')
    unfold mayaSet at h'; simp only [h, h', Bool.false_eq_true, ite_false, Finsupp.mapDomain_zero]

theorem antitone_of_mem_support_upVec {ν : Fin N → ℕ} (hν : Antitone ν) {μ : Fin N → ℕ}
    (hμ : μ ∈ (upVec (R := R) ν).support) : Antitone μ := by
  classical
  obtain ⟨i, -, hi⟩ := mem_biUnion.mp (Finsupp.support_finsetSum hμ)
  split_ifs at hi with h
  · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hi
    split_ifs at hi with he
    · exact he ▸ RMT.addBox_antitone hν h
    · exact absurd rfl hi
  · simp at hi

theorem antitone_of_mem_support_downVec {ν : Fin N → ℕ} (hν : Antitone ν) (r : ℤ → R)
    {μ : Fin N → ℕ} (hμ : μ ∈ (downVec r ν).support) : Antitone μ := by
  classical
  obtain ⟨i, -, hi⟩ := mem_biUnion.mp (Finsupp.support_finsetSum hμ)
  split_ifs at hi with h
  · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hi
    split_ifs at hi with he
    · exact he ▸ (RMT.removeBox_antitone hν h).1
    · exact absurd rfl hi
  · simp at hi

/-- `mayaSet` intertwines `U` with the hops, on vectors supported on partitions. -/
theorem mapDomain_up {f : (Fin N → ℕ) →₀ R} (hf : ∀ ν ∈ f.support, Antitone ν) :
    Finsupp.mapDomain mayaSet (up N R f) = upHop R (Finsupp.mapDomain mayaSet f) := by
  conv_lhs => rw [← Finsupp.sum_single f]
  conv_rhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, map_sum, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_finsetSum,
    map_sum]
  refine sum_congr rfl fun ν hν => ?_
  rw [← Finsupp.smul_single_one, map_smul, up_single, Finsupp.mapDomain_smul, Finsupp.mapDomain_smul,
    mapDomain_upVec (hf ν hν), Finsupp.mapDomain_single, map_smul, upHop,
    Finsupp.linearCombination_single, one_smul]

/-- `mayaSet` intertwines `D_r` with the hops above the wall `−N`. -/
theorem mapDomain_down (r : ℤ → R) {f : (Fin N → ℕ) →₀ R} (hf : ∀ ν ∈ f.support, Antitone ν) :
    Finsupp.mapDomain mayaSet (down N r f) = downHop (-(N : ℤ)) r (Finsupp.mapDomain mayaSet f) := by
  conv_lhs => rw [← Finsupp.sum_single f]
  conv_rhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, map_sum, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_finsetSum,
    map_sum]
  refine sum_congr rfl fun ν hν => ?_
  rw [down_single, Finsupp.mapDomain_smul, mapDomain_downVec (hf ν hν), Finsupp.mapDomain_single,
    downHop, Finsupp.linearCombination_single]

/-- **Fomin's commutator, on the Maya line**: for the hop operators with a wall at `−N`, on the
Maya set `S` of a partition with at most `N` rows,
`[D_r, U] e_S = (Σ_{x ∈ S} (r(x+1) − r(x)) + [−N ∈ S] r(−N)) e_S`. -/
theorem hop_commutator {ν : Fin N → ℕ} (hν : Antitone ν) (r : ℤ → R) :
    downHop (-(N : ℤ)) r (upHop R (Finsupp.single (mayaSet ν) 1)) -
        upHop R (downHop (-(N : ℤ)) r (Finsupp.single (mayaSet ν) 1)) =
      ((∑ x ∈ mayaSet ν, (r (x + 1) - r x)) +
        if -(N : ℤ) ∈ mayaSet ν then r (-(N : ℤ)) else 0) • Finsupp.single (mayaSet ν) 1 := by
  classical
  have h1 : ∀ μ ∈ (Finsupp.single ν (1 : R)).support, Antitone μ := fun μ hμ => by
    have := mem_singleton.mp (Finsupp.support_single_subset hμ); exact this ▸ hν
  have hu : ∀ μ ∈ (up N R (Finsupp.single ν 1)).support, Antitone μ := fun μ hμ => by
    rw [up_single] at hμ; exact antitone_of_mem_support_upVec hν hμ
  have hd : ∀ μ ∈ (down N r (Finsupp.single ν 1)).support, Antitone μ := fun μ hμ => by
    rw [down_single, one_smul] at hμ; exact antitone_of_mem_support_downVec hν r hμ
  rw [← Finsupp.mapDomain_single (f := mayaSet), ← mapDomain_up h1, ← mapDomain_down r hu,
    ← mapDomain_down r h1, ← mapDomain_up hd, ← Finsupp.mapDomain_sub, commutator_single_maya hν,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

/-! ## Fomin's relation as a constant gradient -/

theorem card_mayaSet {ν : Fin N → ℕ} (hν : Antitone ν) : (mayaSet ν).card = N := by
  rw [mayaSet, card_image_of_injective _ (maya_injective hν), card_univ, Fintype.card_fin]

/-- **The wall site is occupied iff the shape is not full** (row `N − 1` empty). -/
theorem neg_mem_mayaSet_iff {ν : Fin N → ℕ} (hν : Antitone ν) :
    -(N : ℤ) ∈ mayaSet ν ↔ ¬ Full ν := by
  rw [mem_mayaSet]
  unfold Full maya
  constructor
  · rintro ⟨i, hi⟩ hf; have := hf i; have := i.isLt; omega
  · intro hf
    simp only [not_forall, not_lt, Nat.le_zero] at hf
    obtain ⟨j, hj⟩ := hf
    have hN : N - 1 < N := by have := j.isLt; omega
    refine ⟨⟨N - 1, hN⟩, ?_⟩
    have := hν (show j ≤ ⟨N - 1, hN⟩ by rw [Fin.le_def]; simp; omega)
    simp only [hj, Nat.le_zero] at this
    rw [this]; push_cast; omega

/-- **Fomin's relation on the Maya line**: if `r` has constant gradient `a`, the commutator is
`a · N` (the gradient times the number of particles) plus the wall weight `r(−N)` when the wall is
occupied. With `r` affine this is `r(0)` off the full shapes (`a N + r(−N) = r(0)`) and
`r(0) − r(−N)` on them: `commutator_single_affine`, read on fermions. -/
theorem hop_commutator_grad {ν : Fin N → ℕ} (hν : Antitone ν) {r : ℤ → R} {a : R}
    (ha : ∀ x, r (x + 1) - r x = a) :
    downHop (-(N : ℤ)) r (upHop R (Finsupp.single (mayaSet ν) 1)) -
        upHop R (downHop (-(N : ℤ)) r (Finsupp.single (mayaSet ν) 1)) =
      ((N : R) * a + if Full ν then 0 else r (-(N : ℤ))) • Finsupp.single (mayaSet ν) 1 := by
  rw [hop_commutator hν]
  simp_rw [ha]
  rw [sum_const, card_mayaSet hν, nsmul_eq_mul]
  congr 2
  by_cases hf : Full ν
  · rw [ite_eq_left hf, ite_eq_right (by rw [neg_mem_mayaSet_iff hν]; exact not_not.mpr hf)]
  · rw [ite_eq_right hf, ite_eq_left ((neg_mem_mayaSet_iff hν).mpr hf)]

/-! ## ω as particle–hole duality, in a box -/

/-- The Fomin eigenvalue of a Maya set `S` in the window `[L, M − 1]` (walls at both ends):
the gradient of `r` over the particles, plus `r(L)` if the bottom site is occupied, minus `r(M)`
if the top site is occupied. -/
def fominEigen (L M : ℤ) (r : ℤ → R) (S : Finset ℤ) : R :=
  ∑ x ∈ S, (r (x + 1) - r x) + (if L ∈ S then r L else 0) - (if M - 1 ∈ S then r M else 0)

/-- `ω` on Maya sets in the window `[L, M − 1]`: the holes, reflected by `y ↦ −1 − y`, as particles
in the window `[−M, −L − 1]`. -/
def conjBox (L M : ℤ) (S : Finset ℤ) : Finset ℤ := (Icc L (M - 1) \ S).image fun y => -1 - y

/-- **Particle–hole duality of Fomin's commutator**: in a box, `ω` exchanges the two walls and
reflects the contents, and the eigenvalue of `S` for `r` is that of `ωS` for `r(−·)`. -/
theorem sum_Icc_grad (r : ℤ → R) (L : ℤ) (n : ℕ) :
    ∑ x ∈ Icc L (L + n - 1), (r (x + 1) - r x) = r (L + n) - r L := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : Icc L (L + (n + 1 : ℕ) - 1) = insert (L + n) (Icc L (L + n - 1)) := by
      ext x; simp only [mem_insert, mem_Icc]; push_cast; omega
    rw [e, sum_insert (by simp), ih]; push_cast; ring_nf

theorem fominEigen_conjBox (L M : ℤ) (r : ℤ → R) {S : Finset ℤ} (hS : S ⊆ Icc L (M - 1))
    (hLM : L < M) :
    fominEigen (-M) (-L) (fun u => r (-u)) (conjBox L M S) = fominEigen L M r S := by
  have hinj : Set.InjOn (fun y : ℤ => -1 - y) ↑(Icc L (M - 1) \ S) := fun a _ b _ h => by
    simp only at h; omega
  have tele : ∑ x ∈ Icc L (M - 1), (r (x + 1) - r x) = r M - r L := by
    have := sum_Icc_grad r L (M - L).toNat
    rw [show L + ((M - L).toNat : ℤ) = M by omega] at this
    exact this
  have split := sum_sdiff hS (f := fun x => r (x + 1) - r x)
  have hbot : -M ∈ conjBox L M S ↔ M - 1 ∉ S := by
    simp only [conjBox, mem_image, mem_sdiff, mem_Icc]
    constructor
    · rintro ⟨y, ⟨-, hy⟩, he⟩; rwa [show y = M - 1 by omega] at hy
    · intro h; exact ⟨M - 1, ⟨⟨by omega, le_rfl⟩, h⟩, by ring⟩
  have htop : -L - 1 ∈ conjBox L M S ↔ L ∉ S := by
    simp only [conjBox, mem_image, mem_sdiff, mem_Icc]
    constructor
    · rintro ⟨y, ⟨-, hy⟩, he⟩; rwa [show y = L by omega] at hy
    · intro h; exact ⟨L, ⟨⟨le_rfl, by omega⟩, h⟩, by ring⟩
  have hsum : ∑ x ∈ conjBox L M S, (r (-(x + 1)) - r (-x)) =
      -∑ y ∈ Icc L (M - 1) \ S, (r (y + 1) - r y) := by
    unfold conjBox
    rw [sum_image hinj, ← sum_neg_distrib]
    refine sum_congr rfl fun y _ => ?_; ring_nf
  unfold fominEigen
  simp only [neg_neg]
  rw [hsum]
  by_cases h1 : L ∈ S <;> by_cases h2 : M - 1 ∈ S
  · rw [ite_eq_right (fun h => hbot.mp h h2), ite_eq_right (fun h => htop.mp h h1),
      ite_eq_left h1, ite_eq_left h2]
    linear_combination -split - tele
  · rw [ite_eq_left (hbot.mpr h2), ite_eq_right (fun h => htop.mp h h1),
      ite_eq_left h1, ite_eq_right h2]
    linear_combination -split - tele
  · rw [ite_eq_right (fun h => hbot.mp h h2), ite_eq_left (htop.mpr h1),
      ite_eq_right h1, ite_eq_left h2]
    linear_combination -split - tele
  · rw [ite_eq_left (hbot.mpr h2), ite_eq_left (htop.mpr h1),
      ite_eq_right h1, ite_eq_right h2]
    linear_combination -split - tele

end Commutator

end RMT.Symmetric.Corners
