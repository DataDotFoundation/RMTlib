import RMTlib.Moments.Theorem3UNLow
import RMTlib.Frames.Places

/-!
# Theorem 3 for `U(N)` read through the places frame

Loop 1 of `docs/loops/`: `RMTlib.Moments` read through the places frame
(`RMT.Frames.places`, our reading of Scholze's programme, not his claim), with RMTlib's
binding `RMT.Frames.placesBinding`.

As first written, the moment polynomial `∏_{i,j<k} (N + i + j + 1)/(i + j + 1)` is not stated in the
frame's vocabulary, so the frame reads nothing in `RMTlib.Moments`. Here it is restated:

* the `k × k` square `square k` as a Young diagram;
* `momentPoly k = C (∏ w)⁻¹ * contentProd (archContent (X + k)) (square k)`
  (`momentPoly_eq_contentProd`): reflecting the row index, `i + j + 1 = k + (j − i')`, so the
  moment polynomial is the archimedean content product of the square, at `N + k`;
* Theorem 3 in that form (`theorem3_iff_contentProd`).

The frame then proposes the finite-place twin: the same statement with `finContent` in place of
`archContent`. Its polynomial is `C (∏ w)⁻¹ * (X + k)^{k²}`, the contents dropped (`twinPoly`).

* The twin agrees with the moment polynomial in the top two coefficients, for every `k`
  (`twinPoly_coeff_eq`, `M ≤ 1`): the contents of the square sum to `0`. So the twin of Theorem 3
  holds for `M ≤ 1` (`theorem3Twin_le_one`), exactly the range in which Theorem 3 is proved.
* It differs at `M = 2` already for `k = 2` (`twinPoly_coeff_two_ne`): `24/12` against `23/12`.
  So Theorem 3 and its twin cannot both hold at `(2, 2)` (`not_theorem3_and_twin_two_two`); Theorem
  3 is checked there, so the twin fails. The defect is `−Σ c²/2` over the cells, the second content
  moment (an algebraic identity when `Σ c = 0`; not formalised here).
-/

open Polynomial Finset RMT.Symmetric RMT.Frames

namespace RMT.UN

/-- The `k × k` square, as a Young diagram. -/
def square (k : ℕ) : YoungDiagram where
  cells := range k ×ˢ range k
  isLowerSet := by
    intro a b hba ha
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at ha ⊢
    exact ⟨lt_of_le_of_lt hba.1 ha.1, lt_of_le_of_lt hba.2 ha.2⟩

theorem square_cells (k : ℕ) : (square k).cells = range k ×ˢ range k := rfl

theorem card_square (k : ℕ) : (square k).cells.card = k * k := by
  simp [square_cells]

/-- The product of the shifted weights, as a product over the square. -/
theorem prod_weights_map (k : ℕ) :
    ((weights k).map fun r => X + C r).prod
      = ∏ c : Fin k × Fin k, (X + C ((c.1 : ℚ) + c.2 + 1)) := by
  simp only [weights, Multiset.map_map, Function.comp_def]
  rfl

/-- **The moment polynomial is the archimedean content product of the square**, at `N + k`. -/
theorem momentPoly_eq_contentProd (k : ℕ) :
    momentPoly k = C ((weights k).prod)⁻¹ * contentProd (archContent (X + C (k : ℚ))) (square k) := by
  rw [momentPoly, prod_weights_map]
  congr 1
  rw [contentProd, square_cells]
  refine Finset.prod_bij (fun c _ => ((Fin.rev c.1 : ℕ), (c.2 : ℕ))) ?_ ?_ ?_ ?_
  · intro c _
    simp only [mem_product, mem_range]
    exact ⟨(Fin.rev c.1).isLt, c.2.isLt⟩
  · intro a _ b _ h
    simp only [Prod.mk.injEq, Fin.val_inj, Fin.rev_inj] at h
    exact Prod.ext h.1 h.2
  · intro b hb
    simp only [mem_product, mem_range] at hb
    refine ⟨(Fin.rev ⟨b.1, hb.1⟩, ⟨b.2, hb.2⟩), mem_univ _, ?_⟩
    simp
  · intro c _
    have h1 : (c.1 : ℕ) < k := c.1.isLt
    simp only [archContent, RMT.Symmetric.content, Fin.val_rev]
    have : (((k - (c.1 + 1) : ℕ) : ℤ)) = (k : ℤ) - c.1 - 1 := by omega
    rw [this]
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    simp only [← C_eq_natCast, ← C_1, ← C_sub]
    rw [add_assoc (X : ℚ[X]), ← C_add]
    congr 2
    ring

/-- **Theorem 3, stated in the places frame's vocabulary.** -/
theorem theorem3_iff_contentProd : Theorem3 ↔ ∀ k M : ℕ, M ≤ k * k →
    thm3Coeff k M = (C ((weights k).prod)⁻¹ *
      contentProd (archContent (X + C (k : ℚ))) (square k)).coeff (k * k - M) := by
  simp only [Theorem3, momentPoly_eq_contentProd]

/-- The finite-place twin of the moment polynomial: the contents dropped. -/
noncomputable def twinPoly (k : ℕ) : ℚ[X] :=
  C ((weights k).prod)⁻¹ * contentProd (finContent (X + C (k : ℚ))) (square k)

theorem twinPoly_eq (k : ℕ) : twinPoly k = C ((weights k).prod)⁻¹ * (X + C (k : ℚ)) ^ (k * k) := by
  rw [twinPoly, contentProd_finContent, card_square]

theorem twinPoly_coeff (k M : ℕ) (hM : M ≤ k * k) :
    (twinPoly k).coeff (k * k - M) = (k : ℚ) ^ M * ((k * k).choose M : ℚ) / (weights k).prod := by
  rw [twinPoly_eq, coeff_C_mul, coeff_X_add_C_pow, Nat.sub_sub_self hM, Nat.choose_symm hM,
    div_eq_inv_mul]

/-- **The twin agrees with the moment polynomial in the top two coefficients**: the contents of
the square sum to `0`. -/
theorem twinPoly_coeff_eq (k M : ℕ) (hM : M ≤ 1) :
    (twinPoly k).coeff (k * k - M) = (momentPoly k).coeff (k * k - M) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · interval_cases M <;> simp [twinPoly_eq, momentPoly, weights]
  have hMk : M ≤ k * k := le_trans hM (Nat.one_le_iff_ne_zero.mpr (by positivity))
  rw [twinPoly_coeff k M hMk, momentPoly_coeff k M hMk]
  interval_cases M
  · simp [exactCoeff, Multiset.esymm, Multiset.powersetCard_zero_left]
  · rw [exactCoeff, Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
    simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id']
    rw [weights_sum_eq, Nat.choose_one_right]
    push_cast
    ring

/-- The twin of Theorem 3 (the statement the frame proposes), for given `k` and `M`. -/
def Theorem3TwinAt (k M : ℕ) : Prop :=
  thm3Coeff k M = (C ((weights k).prod)⁻¹ *
    contentProd (finContent (X + C (k : ℚ))) (square k)).coeff (k * k - M)

/-- **The twin of Theorem 3 holds for `M ≤ 1`**, for every `k ≥ 1`: there the contents do not
matter, and Theorem 3 is proved (`theorem3_zero`, `theorem3_one`). -/
theorem theorem3Twin_le_one (k M : ℕ) (hk : 1 ≤ k) (hM : M ≤ 1) : Theorem3TwinAt k M := by
  rw [Theorem3TwinAt, ← twinPoly, twinPoly_coeff_eq k M hM]
  interval_cases M
  · exact theorem3_zero k
  · exact theorem3_one k hk

/-- `e₂(1, 2, 2, 3) = 23`: the second elementary symmetric function of the weights of the `2 × 2`
square. -/
theorem esymm_two_weights_two : (weights 2).esymm 2 = 23 := by
  rw [weights, Finset.esymm_map_val]
  rw [show (Finset.univ : Finset (Fin 2 × Fin 2)).powersetCard 2 =
      {{(0,0),(0,1)},{(0,0),(1,0)},{(0,0),(1,1)},{(0,1),(1,0)},{(0,1),(1,1)},{(1,0),(1,1)}} by decide]
  simp (config := {decide := true}) [Finset.sum_insert, Finset.prod_insert]
  norm_num

/-- **The twin differs from the moment polynomial at `M = 2`**, already for `k = 2`:
`24/12` against `23/12`. -/
theorem twinPoly_coeff_two_ne : (twinPoly 2).coeff (2 * 2 - 2) ≠ (momentPoly 2).coeff (2 * 2 - 2) := by
  rw [twinPoly_coeff 2 2 (by norm_num), momentPoly_coeff 2 2 (by norm_num), exactCoeff,
    esymm_two_weights_two]
  have hP : (weights 2).prod ≠ 0 := by
    intro h
    have := weights_prod_mul_ksConst 2
    rw [h, zero_mul] at this
    exact zero_ne_one this
  intro h
  field_simp at h
  rw [show Nat.choose 4 2 = 6 by decide] at h
  norm_num at h

/-- **Theorem 3 and its finite-place twin cannot both hold at `(k, M) = (2, 2)`.** Theorem 3 at
`(2, 2)` is checked by `#guard` (`RMTlibExamples/Theorem3UN.lean`), so the twin fails there. -/
theorem not_theorem3_and_twin_two_two :
    ¬ (thm3Coeff 2 2 = (momentPoly 2).coeff (2 * 2 - 2) ∧ Theorem3TwinAt 2 2) := by
  rintro ⟨h1, h2⟩
  rw [Theorem3TwinAt, ← twinPoly] at h2
  exact twinPoly_coeff_two_ne (h2.symm.trans h1)

end RMT.UN
