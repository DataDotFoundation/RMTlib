import RMTlib.Symmetric.CornerMoments

/-!
# A weighted up operator: the product rule, sl₂, and conjugation by `x^K`

`RMT.Symmetric.Corners.up` adds a box with weight `1`. Here `U_u` (`upW`) adds a box `□` with
weight `u(c(□))`. Off the diagonal the two orders still cancel (a box added in row `i` and one
removed in row `j ≠ i` carry the same two weights in either order), so

  `[D_r, U_u] e_ν = (Σ_add r u − Σ_rem r u) e_ν`   (`commutator_weighted_single`):

**only the product `r u` matters.** Consequences:

* **Fomin's form for a product.** If `r u` is affine, `[D_r, U_u] = (r u)(0)` on partitions of
  length `< N` (`commutator_weighted_of_not_full`).
* **sl₂.** For affine `r = a c + b`, `u = a' c + b'`, the product is quadratic and
  `[D_r, U_u] e_ν = (b b' + 2 a a' |ν|) e_ν` (`commutator_weighted_affine_affine`), from the second
  corner moment `Σ_add c² − Σ_rem c² = 2|ν|` (`sum_corners_sq`). With `a = a' = 1` this is
  Okounkov's sl₂ of the z-measures (`[D, U] = L`, `L e_λ = (zz' + 2|λ|) e_λ`): `U` adds a box
  with weight `z + c`, `D` removes one with weight `z' + c` (`sl2_commutator`). Its fermionic twin
  `a' = −1` has `zz' − 2|ν|` (`sl2_commutator_twin`).
* **Conjugation by `x^K`.** Let `K` be the cut-and-join operator, `K e_ν = κ(ν) e_ν` with
  `κ(ν) = Σ_{□ ∈ ν} c(□)` (`contentSum`), and `x` a unit. Then `x^K D_r x^{−K} = D_{r x^{−c}}` and
  `x^K U_u x^{−K} = U_{u x^{c}}` (`twist_down`, `twist_upW`): the `q`-content weights are the
  conjugates of the affine ones. In particular `[D_{ρ x^{−c}}, U_{x^c}] = ρ(0)` for affine `ρ`
  (`commutator_twisted_of_not_full`): **Fomin's form survives the `q`-deformation, with a
  conjugated `U`.** The ω-twin is `x ↦ x⁻¹`.
-/

open Finset

noncomputable section

namespace RMT.Symmetric.Corners

variable {N : ℕ} {R : Type*} [CommRing R]

/-! ## The weighted up operator -/

/-- `U_u e_ν = Σ_{i addable} u(ν_i − i) e_{ν + e_i}`: add a box with weight `u(c)`. -/
def upVecW (u : ℤ → R) (ν : Fin N → ℕ) : (Fin N → ℕ) →₀ R :=
  ∑ i, if RMT.IsAddable ν i then Finsupp.single (RMT.addBox ν i) (u ((ν i : ℤ) - i)) else 0

variable (N) in
/-- **The weighted up operator** `U_u`. -/
def upW (u : ℤ → R) : ((Fin N → ℕ) →₀ R) →ₗ[R] ((Fin N → ℕ) →₀ R) :=
  Finsupp.linearCombination R (upVecW u)

theorem upW_single (u : ℤ → R) (ν : Fin N → ℕ) (c : R) :
    upW N u (Finsupp.single ν c) = c • upVecW u ν := by
  simp [upW]

/-- Weight `1` is Young's lattice's `U`. -/
theorem upW_one : upW N (fun _ => (1 : R)) = up N R := by
  unfold upW up
  rfl

/-- **The product rule**: `[D_r, U_u] e_ν = (Σ_add r u − Σ_rem r u) e_ν`. -/
theorem commutator_weighted_single {ν : Fin N → ℕ} (hν : Antitone ν) (r u : ℤ → R) :
    down N r (upW N u (Finsupp.single ν 1)) - upW N u (down N r (Finsupp.single ν 1)) =
      ((∑ i, if RMT.IsAddable ν i then r ((ν i : ℤ) - i) * u ((ν i : ℤ) - i) else 0) -
        (∑ i, if RMT.IsCorner ν i then r ((ν i : ℤ) - 1 - i) * u ((ν i : ℤ) - 1 - i) else 0)) •
        Finsupp.single ν 1 := by
  classical
  set T1 : Fin N → Fin N → (Fin N → ℕ) →₀ R := fun i j =>
    if RMT.IsAddable ν i && RMT.IsCorner (RMT.addBox ν i) j then
      Finsupp.single (RMT.removeBox (RMT.addBox ν i) j)
        (u ((ν i : ℤ) - i) * r (((RMT.addBox ν i) j : ℤ) - 1 - j))
    else 0 with hT1
  set T2 : Fin N → Fin N → (Fin N → ℕ) →₀ R := fun i j =>
    if RMT.IsCorner ν j && RMT.IsAddable (RMT.removeBox ν j) i then
      Finsupp.single (RMT.addBox (RMT.removeBox ν j) i)
        (r ((ν j : ℤ) - 1 - j) * u (((RMT.removeBox ν j) i : ℤ) - i))
    else 0 with hT2
  have h1 : down N r (upW N u (Finsupp.single ν 1)) = ∑ i, ∑ j, T1 i j := by
    rw [upW_single, one_smul, upVecW, map_sum]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : RMT.IsAddable ν i
    · rw [if_pos hi, down_single, downVec, smul_sum]
      refine sum_congr rfl fun j _ => ?_
      simp only [hT1, hi, Bool.true_and]
      split_ifs
      · rw [Finsupp.smul_single, smul_eq_mul]
      · rw [smul_zero]
    · rw [if_neg hi, map_zero]
      exact (sum_eq_zero fun j _ => by simp [hT1, hi]).symm
  have h2 : upW N u (down N r (Finsupp.single ν 1)) = ∑ i, ∑ j, T2 i j := by
    rw [sum_comm, down_single, one_smul, downVec, map_sum]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : RMT.IsCorner ν j
    · rw [if_pos hj, upW_single, upVecW, smul_sum]
      refine sum_congr rfl fun i _ => ?_
      simp only [hT2, hj, Bool.true_and]
      split_ifs
      · rw [Finsupp.smul_single, smul_eq_mul]
      · rw [smul_zero]
    · rw [if_neg hj, map_zero]
      exact (sum_eq_zero fun i _ => by simp [hT2, hj]).symm
  rw [h1, h2, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  have hdiag : ∀ i, ∑ j, (T1 i j - T2 i j) = T1 i i - T2 i i := by
    intro i
    refine sum_eq_single i (fun j _ hji => ?_) (by simp)
    have e1 : RMT.addBox ν i j = ν j := by simp [RMT.addBox, Function.update_of_ne hji]
    have e2 : RMT.removeBox ν j i = ν i := by
      simp [RMT.removeBox, Function.update_of_ne (Ne.symm hji)]
    simp only [hT1, hT2, addable_corner_iff hν (Ne.symm hji),
      removeBox_addBox_comm (Ne.symm hji), e1, e2]
    split_ifs
    · rw [mul_comm, sub_self]
    · exact sub_self _
  simp_rw [hdiag]
  rw [sum_smul]
  refine sum_congr rfl fun i _ => ?_
  simp only [hT1, hT2]
  have eA : ((RMT.addBox ν i i : ℕ) : ℤ) - 1 - i = (ν i : ℤ) - i := by
    simp [RMT.addBox]
  by_cases ha : RMT.IsAddable ν i <;> by_cases hc : RMT.IsCorner ν i
  · have hc' := RMT.isCorner_addBox hν i
    have hpos := (RMT.removeBox_antitone hν hc).2
    have ha' := RMT.isAddable_removeBox hν hpos
    have eR : ((RMT.removeBox ν i i : ℕ) : ℤ) - i = (ν i : ℤ) - 1 - i := by
      simp [RMT.removeBox]; omega
    simp only [ha, hc, hc', ha', Bool.true_and, if_true, RMT.removeBox_addBox,
      RMT.addBox_removeBox hpos, eA, eR, ← Finsupp.single_sub]
    rw [Finsupp.smul_single_one]; congr 1; ring
  · have hc' := RMT.isCorner_addBox hν i
    simp only [ha, hc, hc', Bool.true_and, Bool.false_and, if_true, RMT.removeBox_addBox,
      if_false, Bool.false_eq_true, sub_zero, eA]
    rw [Finsupp.smul_single_one]; congr 1; ring
  · have hpos := (RMT.removeBox_antitone hν hc).2
    have ha' := RMT.isAddable_removeBox hν hpos
    have eR : ((RMT.removeBox ν i i : ℕ) : ℤ) - i = (ν i : ℤ) - 1 - i := by
      simp [RMT.removeBox]; omega
    simp only [ha, hc, ha', Bool.true_and, Bool.false_and, if_true, if_false, Bool.false_eq_true,
      RMT.addBox_removeBox hpos, zero_sub, eR]
    rw [neg_smul, Finsupp.smul_single_one]
  · simp [ha, hc]

/-- **Fomin's form for a product**: if `r u` is affine, `[D_r, U_u] = (r u)(0)` on every
partition of length `< N`. -/
theorem commutator_weighted_of_not_full {ν : Fin N → ℕ} (hν : Antitone ν) (hfull : ¬ Full ν)
    {r u : ℤ → R} (hru : IsAffine (fun c => r c * u c)) :
    down N r (upW N u (Finsupp.single ν 1)) - upW N u (down N r (Finsupp.single ν 1)) =
      (r 0 * u 0) • Finsupp.single ν 1 := by
  rw [commutator_weighted_single hν,
    sum_corners_affine (r := fun c => r c * u c) hν hru, if_neg hfull, sub_zero]

/-! ## sl₂: two affine weights -/

/-- **The second corner moment on the genuine corners**:
`Σ_add c² − Σ_rem c² = 2|ν| − [ν full] N²`. -/
theorem sum_corners_sq {ν : Fin N → ℕ} (hν : Antitone ν) :
    (∑ i, if RMT.IsAddable ν i then ((((ν i : ℤ) - i : ℤ)) : R) ^ 2 else 0) -
        (∑ i, if RMT.IsCorner ν i then ((((ν i : ℤ) - 1 - i : ℤ)) : R) ^ 2 else 0) =
      2 * ∑ i, (ν i : R) - (if Full ν then (N : R) ^ 2 else 0) := by
  have hM : ∀ i, ν i ≤ univ.sup ν := fun i => le_sup (mem_univ i)
  rw [sum_corners_eq_sum_charge (g := fun c : ℤ => ((c : R)) ^ 2) hν hM, sum_charge_sq hν hM]
  simp

/-- **sl₂ from two affine weights**: for `r = a c + b`, `u = a' c + b'`,
`[D_r, U_u] e_ν = (b b' + 2 a a' |ν|) e_ν` on partitions of length `< N`. -/
theorem commutator_weighted_affine_affine {ν : Fin N → ℕ} (hν : Antitone ν) (hfull : ¬ Full ν)
    (a b a' b' : R) :
    down N (fun c => a * c + b) (upW N (fun c => a' * c + b') (Finsupp.single ν 1)) -
        upW N (fun c => a' * c + b') (down N (fun c => a * c + b) (Finsupp.single ν 1)) =
      (b * b' + 2 * (a * a') * ∑ i, (ν i : R)) • Finsupp.single ν 1 := by
  have hM : ∀ i, ν i ≤ univ.sup ν := fun i => le_sup (mem_univ i)
  rw [commutator_weighted_single hν,
    sum_corners_eq_sum_charge (g := fun c : ℤ => (a * c + b) * (a' * c + b')) hν hM, if_neg hfull,
    sub_zero]
  congr 1
  have h : ∀ c : ℤ, (charge ν c : R) * ((a * c + b) * (a' * c + b')) =
      (a * a') * ((charge ν c : R) * (c : R) ^ 2) + (a * b' + a' * b) * ((charge ν c : R) * c) +
        b * b' * (charge ν c : R) := fun c => by ring
  simp_rw [h]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, sum_charge_sq hν hM,
    sum_charge_id hν hM, sum_charge_one hν hM]
  ring

/-- **Okounkov's sl₂ of the z-measures**: `U` adds a box with weight `z + c`, `D` removes one
with weight `z' + c`, and `[D, U] e_λ = (z z' + 2|λ|) e_λ`. -/
theorem sl2_commutator {ν : Fin N → ℕ} (hν : Antitone ν) (hfull : ¬ Full ν) (z z' : R) :
    down N (fun c => z' + c) (upW N (fun c => z + c) (Finsupp.single ν 1)) -
        upW N (fun c => z + c) (down N (fun c => z' + c) (Finsupp.single ν 1)) =
      (z * z' + 2 * ∑ i, (ν i : R)) • Finsupp.single ν 1 := by
  rw [show (fun c : ℤ => z' + (c : R)) = fun c : ℤ => 1 * (c : R) + z' from funext fun _ => by ring,
    show (fun c : ℤ => z + (c : R)) = fun c : ℤ => 1 * (c : R) + z from funext fun _ => by ring,
    commutator_weighted_affine_affine hν hfull]
  congr 1; ring

/-- **The fermionic twin**: against the dual weight `z − c` the Cartan element is
`z z' − 2|λ|`, which lowers along `U`; at `z = z' = k` the module is finite (the `k × k` box). -/
theorem sl2_commutator_twin {ν : Fin N → ℕ} (hν : Antitone ν) (hfull : ¬ Full ν) (z z' : R) :
    down N (fun c => z' + c) (upW N (fun c => z - c) (Finsupp.single ν 1)) -
        upW N (fun c => z - c) (down N (fun c => z' + c) (Finsupp.single ν 1)) =
      (z * z' - 2 * ∑ i, (ν i : R)) • Finsupp.single ν 1 := by
  rw [show (fun c : ℤ => z' + (c : R)) = fun c : ℤ => 1 * (c : R) + z' from funext fun _ => by ring,
    show (fun c : ℤ => z - (c : R)) = fun c : ℤ => -1 * (c : R) + z from funext fun _ => by ring,
    commutator_weighted_affine_affine hν hfull]
  congr 1; ring

/-! ## Conjugation by `x^K` -/

/-- **The content sum** `κ(ν) = Σ_{□ ∈ ν} c(□) = Σ_i Σ_{j < ν_i} (j − i)`, the eigenvalue of the
cut-and-join operator `K`. -/
def contentSum (ν : Fin N → ℕ) : ℤ := ∑ i, ∑ j ∈ range (ν i), ((j : ℤ) - i)

/-- Adding a box in row `i` adds its content `ν_i − i`. -/
theorem contentSum_addBox (ν : Fin N → ℕ) (i : Fin N) :
    contentSum (RMT.addBox ν i) = contentSum ν + ((ν i : ℤ) - i) := by
  classical
  unfold contentSum RMT.addBox
  rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ _ (mem_univ i),
    Function.update_self, sum_range_succ]
  have : ∑ k ∈ univ.erase i, ∑ j ∈ range (Function.update ν i (ν i + 1) k), ((j : ℤ) - k) =
      ∑ k ∈ univ.erase i, ∑ j ∈ range (ν k), ((j : ℤ) - k) :=
    sum_congr rfl fun k hk => by rw [Function.update_of_ne (ne_of_mem_erase hk)]
  rw [this]; ring

/-- Removing a box from a nonempty row `i` removes its content `ν_i − 1 − i`. -/
theorem contentSum_removeBox (ν : Fin N → ℕ) (i : Fin N) (h : 0 < ν i) :
    contentSum (RMT.removeBox ν i) = contentSum ν - ((ν i : ℤ) - 1 - i) := by
  have := contentSum_addBox (RMT.removeBox ν i) i
  rw [RMT.addBox_removeBox h] at this
  have e : ((RMT.removeBox ν i i : ℕ) : ℤ) = (ν i : ℤ) - 1 := by
    simp [RMT.removeBox]; omega
  rw [this, e]; ring

/-- **The diagonal operator `x^K`**: `e_ν ↦ x^{κ(ν)} e_ν`. -/
def twist (x : Rˣ) : ((Fin N → ℕ) →₀ R) →ₗ[R] ((Fin N → ℕ) →₀ R) :=
  Finsupp.linearCombination R fun ν => Finsupp.single ν ((x ^ contentSum ν : Rˣ) : R)

theorem twist_single (x : Rˣ) (ν : Fin N → ℕ) (c : R) :
    twist x (Finsupp.single ν c) = Finsupp.single ν (c * ((x ^ contentSum ν : Rˣ) : R)) := by
  simp [twist, Finsupp.smul_single]

theorem pos_of_isCorner {ν : Fin N → ℕ} {i : Fin N} (hc : RMT.IsCorner ν i = true) :
    0 < ν i := by
  simp only [RMT.IsCorner, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1

/-- **`x^K D_r = D_{r x^{−c}} x^K`**: conjugating by `x^K` multiplies the weight of a removed box
of content `c` by `x^{−c}`. -/
theorem twist_down (x : Rˣ) (r : ℤ → R) :
    twist x ∘ₗ down N r = down N (fun c => r c * ((x ^ (-c) : Rˣ) : R)) ∘ₗ twist x := by
  refine Finsupp.lhom_ext' fun ν => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [down_single, one_smul, twist_single, one_mul, down_single, downVec, downVec, map_sum,
    smul_sum]
  refine sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · rw [twist_single, Finsupp.smul_single, smul_eq_mul, contentSum_removeBox ν i (pos_of_isCorner hc)]
    congr 1
    rw [zpow_sub, ← zpow_neg, Units.val_mul]
    ring
  · rw [map_zero, smul_zero]

/-- **`x^K U_u = U_{u x^{c}} x^K`**: conjugating by `x^K` multiplies the weight of an added box
of content `c` by `x^{c}`. -/
theorem twist_upW (x : Rˣ) (u : ℤ → R) :
    twist x ∘ₗ upW N u = upW N (fun c => u c * ((x ^ c : Rˣ) : R)) ∘ₗ twist x := by
  refine Finsupp.lhom_ext' fun ν => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [upW_single, one_smul, twist_single, one_mul, upW_single, upVecW, upVecW, map_sum,
    smul_sum]
  refine sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [twist_single, Finsupp.smul_single, smul_eq_mul, contentSum_addBox, zpow_add,
      Units.val_mul]
    ring_nf
  · rw [map_zero, smul_zero]

/-- **Fomin's form survives the `q`-deformation**: for affine `ρ` and a unit `x`, the conjugated
pair `D_{ρ x^{−c}}`, `U_{x^c}` has `[D, U] = ρ(0)` on partitions of length `< N`. -/
theorem commutator_twisted_of_not_full {ν : Fin N → ℕ} (hν : Antitone ν) (hfull : ¬ Full ν)
    (x : Rˣ) {ρ : ℤ → R} (hρ : IsAffine ρ) :
    down N (fun c => ρ c * ((x ^ (-c) : Rˣ) : R))
          (upW N (fun c => ((x ^ c : Rˣ) : R)) (Finsupp.single ν 1)) -
        upW N (fun c => ((x ^ c : Rˣ) : R))
          (down N (fun c => ρ c * ((x ^ (-c) : Rˣ) : R)) (Finsupp.single ν 1)) =
      ρ 0 • Finsupp.single ν 1 := by
  have hprod : (fun c : ℤ => ρ c * ((x ^ (-c) : Rˣ) : R) * ((x ^ c : Rˣ) : R)) = ρ := by
    funext c
    rw [mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]
  rw [commutator_weighted_of_not_full hν hfull (by rw [hprod]; exact hρ)]
  simp

end RMT.Symmetric.Corners
