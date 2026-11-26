import RMTlib.Moments.OtherFamilies.SignSums
import RMTlib.Symmetric.FominMaya
import RMTlib.Symmetric.FominSl2

/-!
# The symplectic flavour of boson–fermion

The sign-choice sums of `RMTlib.Moments.OtherFamilies.SignSums` (the "other families" note,
`archives/lower_2`) are a boson–fermion correspondence for `Sp`, in the additive (Lie algebra)
variables of the moment recipe. Write `Δ(k) = (k, k−1, …, 1)`.

* **Shapes.** The partitions with a nonzero type-`C` sign-average are exactly `λ = 2ν + Δ(k)`
  (`sympShape`; `sympShape_halfShape`, `symplectic_sum_eq_zero`), and `ν = halfShape λ`
  (`halfShape_sympShape`). For type `D` they are `2ν + Δ(k−1)` (`orthShape`).
* **Boson = fermion.** `symplectic_boson_fermion`: the fermionic side, the average over
  `ε ∈ {±1}^k` of `s_{2ν+Δ(k)}(εx)` against `∏_{i≤j} (ε_i x_i + ε_j x_j)`, is the bosonic side
  `s_ν(x²)`, a Schur function of the squares. `orthogonal_boson_fermion`: `2^k s_ν(x²)` for
  `2ν + Δ(k−1)` against `∏_{i<j}`.
* **The fermion side is ν's Maya diagram stretched by two.** `maya_sympShape`:
  `b^λ_j = 2 b^ν_j + k + 1`, so the particles of `2ν + Δ(k)` occupy one parity class of sites
  (`maya_orthShape`: the other class, `2 b^ν_j + k`, for type `D`). The sign average is the
  projection onto the odd (type `C`) or even (type `D`) part under `x ↦ −x`.
* **Fomin.** Adding a box to `ν` adds a horizontal domino to `2ν + Δ(k)` (`sympShape_addBox`);
  on the Maya line it is a **double hop** `y ↦ y + 2` over a site of the other class
  (`mayaSet_sympShape_addBox`). So the Fomin operators of `RMTlib.Symmetric.FominMaya` and
  `RMTlib.Symmetric.FominSl2` on `ν` are the domino operators of the symplectic shapes, and their
  commutators transfer unchanged, contents read through `c ↦ 2c + k + 1`.
-/

open Finset RMT.Symmetric

namespace RMT.Moments.OtherFamilies

variable {k : ℕ}

/-- The type-`C` shape `2ν + Δ(k)`: `λ_j = 2ν_j + (k − j)`. -/
def sympShape (ν : Fin k → ℕ) : Fin k → ℕ := fun j => 2 * ν j + stair k j + 1

/-- The type-`D` shape `2ν + Δ(k−1)`: `λ_j = 2ν_j + (k − 1 − j)`. -/
def orthShape (ν : Fin k → ℕ) : Fin k → ℕ := fun j => 2 * ν j + stair k j

theorem sympShape_antitone {ν : Fin k → ℕ} (hν : Antitone ν) : Antitone (sympShape ν) := by
  intro i j hij; have := hν hij; have : (i : ℕ) ≤ j := hij
  simp only [sympShape, stair]; omega

theorem orthShape_antitone {ν : Fin k → ℕ} (hν : Antitone ν) : Antitone (orthShape ν) := by
  intro i j hij; have := hν hij; have : (i : ℕ) ≤ j := hij
  simp only [orthShape, stair]; omega

theorem sympShape_odd (ν : Fin k → ℕ) (j : Fin k) : Odd (sympShape ν j + stair k j) :=
  ⟨ν j + stair k j, by simp only [sympShape]; ring⟩

theorem orthShape_even (ν : Fin k → ℕ) (j : Fin k) : Even (orthShape ν j + stair k j) :=
  ⟨ν j + stair k j, by simp only [orthShape]; ring⟩

theorem halfShape_sympShape (ν : Fin k → ℕ) : halfShape (sympShape ν) = ν := by
  ext j; simp only [halfShape, sympShape]; omega

theorem halfShape_orthShape (ν : Fin k → ℕ) : halfShape (orthShape ν) = ν := by
  ext j; simp only [halfShape, orthShape]; omega

/-- **Every shape with a nonzero symplectic sign-sum is `2ν + Δ(k)`**: if all `λ_j + δ_j` are
odd, then `λ = sympShape (halfShape λ)`. -/
theorem sympShape_halfShape {l : Fin k → ℕ} (hl : Antitone l) (h : ∀ j, Odd (l j + stair k j)) :
    sympShape (halfShape l) = l := by
  have hp : ∀ j, (l j + stair k j) % 2 = 1 := fun j => Nat.odd_iff.mp (h j)
  ext j
  have := stair_add_le hl 1 hp j
  have := hp j
  simp only [sympShape, halfShape]; omega

theorem orthShape_halfShape {l : Fin k → ℕ} (hl : Antitone l) (h : ∀ j, Even (l j + stair k j)) :
    orthShape (halfShape l) = l := by
  have hp : ∀ j, (l j + stair k j) % 2 = 0 := fun j => Nat.even_iff.mp (h j)
  ext j
  have := stair_add_le hl 0 hp j
  have := hp j
  simp only [orthShape, halfShape]; omega

/-! ### Boson–fermion: the sign-average of `2ν + Δ(k)` is `s_ν(x²)` -/

section Field

variable {K : Type*} [Field K]

/-- **Symplectic boson–fermion correspondence**: the fermionic side is the sign-average of the
Schur function of `2ν + Δ(k)` against the type-`C` Weyl denominator; the bosonic side is the Schur
function of `ν` in the squared variables. -/
theorem symplectic_boson_fermion (x : Fin k → K) (hx : altV (sqPt x) k (stair k) ≠ 0)
    (hx0 : ∀ i, x i ≠ 0) (h2 : (2 : K) ≠ 0) {ν : Fin k → ℕ} (hν : Antitone ν) :
    ∑ ε, schurV (signPt x ε) k k (sympShape ν) /
        ∏ i, ∏ j ∈ Ici i, (signVec x ε i + signVec x ε j) = schurV (sqPt x) k k ν := by
  rw [sum_schurV_div_typeC x hx hx0 h2 (sympShape_antitone hν),
    ite_eq_left (sympShape_odd ν), halfShape_sympShape]

/-- **…and only these shapes survive**: a partition that is not `2ν + Δ(k)` averages to `0`. -/
theorem symplectic_sum_eq_zero (x : Fin k → K) (hx : altV (sqPt x) k (stair k) ≠ 0)
    (hx0 : ∀ i, x i ≠ 0) (h2 : (2 : K) ≠ 0) {l : Fin k → ℕ} (hl : Antitone l)
    (hne : ∀ ν, sympShape ν ≠ l) :
    ∑ ε, schurV (signPt x ε) k k l / ∏ i, ∏ j ∈ Ici i, (signVec x ε i + signVec x ε j) = 0 := by
  rw [sum_schurV_div_typeC x hx hx0 h2 hl, ite_eq_right]
  intro h; exact hne _ (sympShape_halfShape hl h)

/-- **The orthogonal (type `D`) flavour**: the sign-average of `2ν + Δ(k−1)` is `2^k s_ν(x²)`. -/
theorem orthogonal_boson_fermion (x : Fin k → K) (hx : altV (sqPt x) k (stair k) ≠ 0)
    {ν : Fin k → ℕ} (hν : Antitone ν) :
    ∑ ε, schurV (signPt x ε) k k (orthShape ν) /
        ∏ i, ∏ j ∈ Ioi i, (signVec x ε i + signVec x ε j) = 2 ^ k * schurV (sqPt x) k k ν := by
  rw [sum_schurV_div_typeD x hx (orthShape_antitone hν),
    ite_eq_left (orthShape_even ν), halfShape_orthShape]

theorem orthogonal_sum_eq_zero (x : Fin k → K) (hx : altV (sqPt x) k (stair k) ≠ 0)
    {l : Fin k → ℕ} (hl : Antitone l) (hne : ∀ ν, orthShape ν ≠ l) :
    ∑ ε, schurV (signPt x ε) k k l / ∏ i, ∏ j ∈ Ioi i, (signVec x ε i + signVec x ε j) = 0 := by
  rw [sum_schurV_div_typeD x hx hl, ite_eq_right]
  intro h; exact hne _ (orthShape_halfShape hl h)

end Field

/-! ### The fermion side: the Maya diagram stretched by two -/

open RMT.Symmetric.Corners in
/-- **The symplectic Maya diagram is `ν`'s stretched by two**: `b^λ_j = 2 b^ν_j + k + 1`, so the
particles of `2ν + Δ(k)` sit on one parity class of sites, and its holes include the other. -/
theorem maya_sympShape (ν : Fin k → ℕ) (j : Fin k) :
    maya (sympShape ν) j = 2 * maya ν j + k + 1 := by
  unfold maya sympShape stair; have := j.isLt; push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + (j : ℕ) ≤ k)]; ring

open RMT.Symmetric.Corners in
theorem mayaSet_sympShape (ν : Fin k → ℕ) :
    mayaSet (sympShape ν) = (mayaSet ν).image fun x : ℤ => 2 * x + (k : ℤ) + 1 := by
  simp only [mayaSet, image_image]
  congr 1; funext j; simp [maya_sympShape]

open RMT.Symmetric.Corners in
/-- The orthogonal Maya diagram is `ν`'s stretched by two, on the other parity class. -/
theorem maya_orthShape (ν : Fin k → ℕ) (j : Fin k) :
    maya (orthShape ν) j = 2 * maya ν j + k := by
  unfold maya orthShape stair; have := j.isLt; push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + (j : ℕ) ≤ k)]; ring

/-! ### Fomin: a box of `ν` is a domino of `λ`, a hop is a double hop -/

/-- **Adding a box to `ν` adds a horizontal domino to `2ν + Δ(k)`.** -/
theorem sympShape_addBox (ν : Fin k → ℕ) (i : Fin k) :
    sympShape (RMT.addBox ν i) = RMT.addBox (RMT.addBox (sympShape ν) i) i := by
  ext j; by_cases h : j = i
  · subst h; simp [sympShape, RMT.addBox]; ring
  · simp [sympShape, RMT.addBox, Function.update_of_ne h]

open RMT.Symmetric.Corners in
/-- **On the Maya line the symplectic up-move is a double hop**: the particle of row `i` moves
from `y` to `y + 2`, over a site of the other parity class (always empty). -/
theorem mayaSet_sympShape_addBox {ν : Fin k → ℕ} (hν : Antitone ν) (i : Fin k) :
    mayaSet (sympShape (RMT.addBox ν i)) =
      hop (mayaSet (sympShape ν)) (maya (sympShape ν) i) (maya (sympShape ν) i + 2) := by
  rw [mayaSet_sympShape, mayaSet_addBox hν, mayaSet_sympShape, maya_sympShape]
  ext x
  simp only [hop, mem_image, mem_insert, mem_erase]
  constructor
  · rintro ⟨y, hy | ⟨hy1, hy2⟩, rfl⟩
    · left; rw [hy]; ring
    · right; exact ⟨fun h => hy1 (by omega), y, hy2, rfl⟩
  · rintro (rfl | ⟨hx, y, hy, rfl⟩)
    · exact ⟨maya ν i + 1, Or.inl rfl, by ring⟩
    · exact ⟨y, Or.inr ⟨fun h => hx (by rw [h]), hy⟩, rfl⟩

/-! ### The mirror wall: `sl₂` in the symplectic shape -/

/-- `|Δ(k)| = Σ_j (k − j) = k(k+1)/2`, without division. -/
theorem two_mul_sum_stair_succ (k : ℕ) : 2 * ∑ j : Fin k, (stair k j + 1) = k * (k + 1) := by
  have e1 : ∑ j : Fin k, (stair k j + 1) = ∑ j ∈ range k, (k - 1 - j + 1) :=
    Fin.sum_univ_eq_sum_range (fun j => k - 1 - j + 1) k
  have e2 : ∑ j ∈ range k, (k - 1 - j + 1) = ∑ j ∈ range k, (j + 1) :=
    Finset.sum_range_reflect (fun j => j + 1) k
  have e3 : ∑ j ∈ range (k + 1), j = ∑ j ∈ range k, (j + 1) := by
    rw [Finset.sum_range_succ']; simp
  have g := Finset.sum_range_id_mul_two (k + 1)
  rw [e1, e2, ← e3, mul_comm, g]; simp [mul_comm]

/-- **The symplectic shift**: `|2ν + Δ(k)| = 2|ν| + |Δ(k)|`. -/
theorem sum_sympShape (ν : Fin k → ℕ) :
    ∑ j, sympShape ν j = 2 * ∑ j, ν j + ∑ j : Fin k, (stair k j + 1) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp only [sympShape]; ring

open RMT.Symmetric.Corners in
/-- **`sl₂` at the mirror wall, read on the symplectic shape**: for `λ = 2ν + Δ(k)`, the `sl₂`
commutator on `ν` (`U` weighted `z + c`, `D` weighted `z' + c`) has eigenvalue
`|λ| − |Δ(k)| + z z'` off the full shapes: twice `L₀` is `|λ|` shifted by the staircase `|Δ(k)|`,
the symplectic `ρ`-shift. -/
theorem sl2_commutator_sympShape {R : Type*} [CommRing R] {ν : Fin k → ℕ} (hν : Antitone ν)
    (z z' : R) :
    down k (fun c => z' + c) (upW k (fun c => z + c) (Finsupp.single ν 1)) -
        upW k (fun c => z + c) (down k (fun c => z' + c) (Finsupp.single ν 1)) =
      (((∑ j, sympShape ν j : ℕ) : R) - ((∑ j : Fin k, (stair k j + 1) : ℕ) : R) + z * z' -
        if Full ν then (z - k) * (z' - k) else 0) • Finsupp.single ν 1 := by
  rw [sl2_commutator_all hν]
  congr 1
  rw [sum_sympShape]; push_cast; ring

end RMT.Moments.OtherFamilies
