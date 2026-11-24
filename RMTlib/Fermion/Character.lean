import RMTlib.Fermion.Rows

/-!
# The character of the boson–fermion correspondence (Jacobi triple product, combinatorial form)

The fermionic Fock space has the basis of Maya diagrams. Its character
`∑_M z^{charge M} q^{energy M}` is a product over sites, since a Maya diagram is a free choice of
particles `P ⊆ ℕ` and holes `H ⊆ ℕ`:

  `∏_{b ≥ 0} (1 + z q^b) · ∏_{h ≥ 0} (1 + z⁻¹ q^{h+1}) = ∑_M z^{charge M} q^{energy M}`

(`fermion_expand`, truncated to the box of sites `< K`; `mem_box_of_energy_lt` says the truncation
is exact in `q`-degree `< K`). The boson–fermion correspondence (`sectorPartitionEquiv`) then
counts each coefficient: in charge `n` and energy `k + n(n − 1)/2` there are `p(k)` Maya diagrams
(`card_box_sector`), `p(k)` being the `k`-th coefficient of Mathlib's partition generating
function `Nat.Partition.genFun` (`card_partition_eq_coeff_genFun`). Together:

  `∏_{b ≥ 0} (1 + z q^b) ∏_{h ≥ 0} (1 + z⁻¹ q^{h+1}) = ∑_{n ∈ ℤ} z^n q^{n(n−1)/2} · ∑_λ q^{|λ|}`,

coefficient by coefficient. With Euler's `∑_λ q^{|λ|} = ∏_{m ≥ 1} (1 − q^m)⁻¹` (not in Mathlib at
this version: `Nat.Partition.genFun` has it as a TODO; not proved here) this is Jacobi's triple
product.

The same expansion holds for any one-body potential `φ`
(`fermion_expand_weight`): `∏_b (1 + z φ(b)) ∏_h (1 + z⁻¹ φ(−h−1)⁻¹) = ∑_M z^{charge M} weight φ M`.
-/

open Finset

namespace RMT.Fermion

open Maya

/-- The Maya diagrams whose particles and holes are all `< K`. -/
def box (K : ℕ) : Finset Maya :=
  ((range K).powerset ×ˢ (range K).powerset).image fun x => ⟨x.1, x.2⟩

theorem mem_box {K : ℕ} {M : Maya} : M ∈ box K ↔ M.P ⊆ range K ∧ M.H ⊆ range K := by
  simp only [box, mem_image, mem_product, mem_powerset]
  constructor
  · rintro ⟨⟨P, H⟩, ⟨hP, hH⟩, rfl⟩; exact ⟨hP, hH⟩
  · rintro ⟨hP, hH⟩; exact ⟨⟨M.P, M.H⟩, ⟨hP, hH⟩, rfl⟩

/-- The box of size `K` contains every Maya diagram of energy `< K`. -/
theorem mem_box_of_energy_lt {K : ℕ} {M : Maya} (hM : M.energy < K) : M ∈ box K := by
  refine mem_box.mpr ⟨fun p hp => mem_range.mpr ?_, fun h hh => mem_range.mpr ?_⟩
  · have := single_le_sum (f := fun p => p) (fun _ _ => Nat.zero_le _) hp
    unfold energy at hM; omega
  · have := single_le_sum (f := fun h => h + 1) (fun _ _ => Nat.zero_le _) hh
    unfold energy at hM; omega

theorem box_injective : Function.Injective fun x : Finset ℕ × Finset ℕ => (⟨x.1, x.2⟩ : Maya) :=
  fun x y h => by
    simp only [Maya.mk.injEq] at h
    exact Prod.ext h.1 h.2

/-- **The fermionic character, with a one-body potential.** For units `z` and `φ(b)`,
`∏_{b < K} (1 + z φ(b)) · ∏_{h < K} (1 + z⁻¹ φ(−h−1)⁻¹) = ∑_{M ∈ box K} z^{charge M} weight φ M`. -/
theorem fermion_expand_weight {R : Type*} [CommRing R] (z : Rˣ) (φ : ℤ → Rˣ) (K : ℕ) :
    (∏ b ∈ range K, (1 + ((z * φ b : Rˣ) : R))) *
        ∏ h ∈ range K, (1 + ((z⁻¹ * (φ (holeSite h))⁻¹ : Rˣ) : R)) =
      ∑ M ∈ box K, ((z ^ M.charge * weight φ M : Rˣ) : R) := by
  rw [prod_one_add, prod_one_add, sum_mul_sum, ← sum_product', box,
    sum_image fun x _ y _ h => box_injective h]
  refine sum_congr rfl fun x _ => ?_
  rw [← Units.coe_prod, ← Units.coe_prod, ← Units.val_mul]
  congr 1
  simp only [prod_mul_distrib, prod_const, prod_inv_distrib, weight, charge]
  rw [zpow_sub, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]
  ac_rfl

/-- **The fermionic character** (Jacobi triple product, product side):
`∏_{b < K} (1 + z q^b) · ∏_{h < K} (1 + z⁻¹ q^{h+1}) = ∑_{M ∈ box K} z^{charge M} q^{energy M}`. -/
theorem fermion_expand {R : Type*} [CommRing R] (z : Rˣ) (q : R) (K : ℕ) :
    (∏ b ∈ range K, (1 + (z : R) * q ^ b)) * ∏ h ∈ range K, (1 + ((z⁻¹ : Rˣ) : R) * q ^ (h + 1)) =
      ∑ M ∈ box K, ((z ^ M.charge : Rˣ) : R) * q ^ M.energy := by
  rw [prod_one_add, prod_one_add, sum_mul_sum, ← sum_product', box,
    sum_image fun x _ y _ h => box_injective h]
  refine sum_congr rfl ?_
  rintro ⟨P, H⟩ _
  simp only [prod_mul_distrib, prod_const, prod_pow_eq_pow_sum, charge, energy]
  rw [zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
    ← inv_pow, Units.val_pow_eq_pow_val, pow_add,
    show ∏ p ∈ P, q ^ p = q ^ ∑ p ∈ P, p from prod_pow_eq_pow_sum _ _ _]
  ring

/-- **The coefficients of the fermionic character are partition numbers.** In a box of size
`K > k + n(n − 1)/2`, the Maya diagrams of charge `n` and energy `k + n(n − 1)/2` are `p(k)` in
number. -/
theorem card_box_sector (n : ℤ) (k K : ℕ) (hK : k + tri n < K) :
    ((box K).filter fun M => M.charge = n ∧ M.energy = k + tri n).card =
      Fintype.card (Nat.Partition k) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (sectorPartitionEquiv n k), ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_)
  simp only [mem_filter]
  constructor
  · exact fun h => h.2
  · rintro ⟨hQ, hE⟩; exact ⟨mem_box_of_energy_lt (M := M) (by omega), hQ, hE⟩

/-- Outside the energies `k + n(n − 1)/2`, the charge-`n` coefficient vanishes. -/
theorem filter_box_eq_empty (n : ℤ) {e : ℕ} (he : e < tri n) (K : ℕ) :
    (box K).filter (fun M => M.charge = n ∧ M.energy = e) = ∅ := by
  refine filter_eq_empty_iff.mpr fun M _ h => ?_
  have := tri_charge_le_energy M
  rw [h.1, h.2] at this
  omega

/-- The bosonic factor: `p(k)` is the `k`-th coefficient of Mathlib's partition generating
function with the trivial character, `∑_λ q^{|λ|}`. -/
theorem card_partition_eq_coeff_genFun (k : ℕ) :
    (Fintype.card (Nat.Partition k) : ℤ) =
      PowerSeries.coeff k (Nat.Partition.genFun fun _ _ => (1 : ℤ)) := by
  rw [Nat.Partition.coeff_genFun]
  simp [Finsupp.prod]

end RMT.Fermion
