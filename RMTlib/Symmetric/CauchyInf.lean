import RMTlib.Symmetric.SSYT
import MeaningLib.Frame.Pattern

/-!
# The Cauchy identity in infinitely many variables

For two injective families of variables `x y : ℕ → ι` with disjoint ranges, the Schur function
`s_μ(x) = ∑' T, x ^ T` over *all* semistandard Young tableaux of shape `μ` (entries in `ℕ`) is a
summable total weight in `MvPowerSeries ι R`, and

  `∑' μ, s_μ(x) s_μ(y) = ∑' A, ∏_{i,j} (x_j y_i) ^ (A i j)`,

the sum on the right over all finitely supported `ℕ`-matrices `A : ℕ × ℕ →₀ ℕ` (`cauchy_inf`).

The proof reduces each coefficient to finitely many variables. `keep V` keeps the monomials whose
variables all lie in `V` and kills the others; it is additive, multiplicative and continuous.
For `V = V_M` the complement of `{x_j, y_i : i, j ≥ M}`, it sends `s_μ(x)` to the Schur
polynomial in `x₀, …, x_{M−1}` and the matrices to those supported in `[0, M)²`, so it sends
both sides to the two sides of `RMT.Symmetric.cauchy_ssyt` with `m = n = M`. Every monomial lies
in some `V_M`.

## Main definitions

* `keep V F`: the monomials of `F` in the variables of `V`.
* `schurInf R x μ`: `∑' T : SSYT μ, X ^ (ssytWt x T)`.
* `matWtInf x y A`: `Σ_{(i, j)} A (i, j) • (x_j + y_i)`.

## Main results

* `finiteFibres_ssytWt`, `finiteFibres_matWtInf`: both are valued sets (for injective `x`, `y`).
* `keep_schurInf`: `keep V_M (s_μ(x)) = s_μ(x₀, …, x_{M−1})`.
* `summable_schurInf_mul`: the family `μ ↦ s_μ(x) s_μ(y)` is summable.
* `cauchy_inf`.
-/

open scoped MvPowerSeries.WithPiTopology
open MvPowerSeries

namespace RMT.Symmetric

/-! ## Keeping the monomials in a set of variables -/

section Keep

variable {ι R : Type*} [CommSemiring R]

open Classical in
/-- `keep V F`: the monomials of `F` all of whose variables lie in `V`. -/
noncomputable def keep (V : Set ι) (F : MvPowerSeries ι R) : MvPowerSeries ι R :=
  fun e => if ↑e.support ⊆ V then coeff e F else 0

open Classical in
theorem coeff_keep (V : Set ι) (F : MvPowerSeries ι R) (e : ι →₀ ℕ) :
    coeff e (keep V F) = if ↑e.support ⊆ V then coeff e F else 0 :=
  rfl

theorem coeff_keep_of_subset (V : Set ι) (F : MvPowerSeries ι R) {e : ι →₀ ℕ}
    (he : ↑e.support ⊆ V) : coeff e (keep V F) = coeff e F := by
  classical
  rw [coeff_keep, ite_eq_left he]

/-- `keep V` as an additive map. -/
noncomputable def keepHom (V : Set ι) : MvPowerSeries ι R →+ MvPowerSeries ι R where
  toFun := keep V
  map_zero' := by
    classical
    ext e
    rw [coeff_keep]
    simp
  map_add' F G := by
    classical
    ext e
    simp only [coeff_keep, map_add]
    split_ifs <;> simp

theorem continuous_keep [TopologicalSpace R] (V : Set ι) :
    Continuous (keep V : MvPowerSeries ι R → MvPowerSeries ι R) := by
  classical
  apply continuous_pi
  intro e
  show Continuous (fun F : MvPowerSeries ι R => if ↑e.support ⊆ V then coeff e F else 0)
  split
  · exact WithPiTopology.continuous_coeff R e
  · exact continuous_const

open Classical in
theorem keep_mono (V : Set ι) (w : ι →₀ ℕ) :
    keep V (mono w : MvPowerSeries ι R) = if ↑w.support ⊆ V then mono w else 0 := by
  ext e
  rw [coeff_keep, coeff_monomial]
  by_cases hw : ↑w.support ⊆ V
  · rw [ite_eq_left hw]
    by_cases he : e = w
    · subst he
      simp [hw]
    · simp [he, coeff_monomial]
  · rw [ite_eq_right hw]
    by_cases he : e = w
    · subst he
      simp [hw]
    · simp [he]

theorem support_subset_of_le {e f : ι →₀ ℕ} (h : e ≤ f) : (e.support : Set ι) ⊆ f.support := by
  intro i hi
  simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hi ⊢
  have := h i
  omega

/-- `keep V` is multiplicative. -/
theorem keep_mul (V : Set ι) (F G : MvPowerSeries ι R) :
    keep V (F * G) = keep V F * keep V G := by
  classical
  ext e
  rw [coeff_keep, coeff_mul, coeff_mul]
  split_ifs with he
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_antidiagonal] at hp
    have h1 : p.1 ≤ e := by rw [← hp]; exact le_self_add
    have h2 : p.2 ≤ e := by rw [← hp]; exact le_add_self
    rw [coeff_keep_of_subset V F (subset_trans (support_subset_of_le h1) he),
      coeff_keep_of_subset V G (subset_trans (support_subset_of_le h2) he)]
  · symm
    refine Finset.sum_eq_zero (fun p hp => ?_)
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_keep, coeff_keep]
    by_cases h1 : ↑p.1.support ⊆ V
    · by_cases h2 : ↑p.2.support ⊆ V
      · exfalso
        apply he
        intro i hi
        simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hi
        rw [← hp] at hi
        simp only [Finsupp.add_apply] at hi
        by_cases h : p.1 i = 0
        · exact h2 (by simp only [Finset.mem_coe, Finsupp.mem_support_iff]; omega)
        · exact h1 (by simp only [Finset.mem_coe, Finsupp.mem_support_iff]; exact h)
      · rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- `keep V` commutes with summable sums. -/
theorem keep_tsum [TopologicalSpace R] [T2Space R] {A : Type*} {f : A → MvPowerSeries ι R}
    (hf : Summable f) (V : Set ι) : keep V (∑' a, f a) = ∑' a, keep V (f a) :=
  hf.map_tsum (keepHom V) (continuous_keep V)

end Keep

/-! ## Schur functions in infinitely many variables -/

section Inf

variable {ι : Type*}

theorem one_le_ssytWt (x : ℕ → ι) {μ : YoungDiagram} (T : SemistandardYoungTableau μ)
    {i j : ℕ} (hc : (i, j) ∈ μ) : 1 ≤ ssytWt x T (x (T i j)) := by
  classical
  simp only [ssytWt, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine le_trans ?_ (Finset.single_le_sum (f := fun c : ℕ × ℕ =>
    (Finsupp.single (x (T c.1 c.2)) 1 : ι →₀ ℕ) (x (T i j))) (fun _ _ => Nat.zero_le _)
    hc)
  simp

theorem exists_of_mem_support_ssytWt (x : ℕ → ι) {μ : YoungDiagram}
    (T : SemistandardYoungTableau μ) {v : ι} (hv : v ∈ (ssytWt x T).support) :
    ∃ i j, (i, j) ∈ μ ∧ x (T i j) = v := by
  classical
  have := Finsupp.support_finsetSum hv
  simp only [Finset.mem_biUnion] at this
  obtain ⟨c, hc, hv'⟩ := this
  have := Finsupp.support_single_subset hv'
  simp only [Finset.mem_singleton] at this
  exact ⟨c.1, c.2, hc, this.symm⟩

theorem degree_ssytWt (x : ℕ → ι) {μ : YoungDiagram} (T : SemistandardYoungTableau μ) :
    Finsupp.degree (ssytWt x T) = μ.cells.card := by
  simp [ssytWt, map_sum, Finsupp.degree_single]

/-- Tableaux of shape `μ` with bounded entries are finitely many. -/
theorem finite_ssyt_lt (μ : YoungDiagram) (K : ℕ) :
    {T : SemistandardYoungTableau μ | ∀ i j, (i, j) ∈ μ → T i j < K}.Finite := by
  apply Set.Finite.of_finite_image (f := fun T : SemistandardYoungTableau μ =>
    fun c : μ.cells => T c.1.1 c.1.2)
  · apply (Set.Finite.pi (t := fun _ : μ.cells => Set.Iio K) (fun _ => Set.finite_Iio K)).subset
    rintro _ ⟨T, hT, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iio]
    intro c
    exact hT _ _ c.2
  · intro T _ T' _ h
    ext i j
    by_cases hc : (i, j) ∈ μ
    · exact congrFun h ⟨(i, j), hc⟩
    · rw [T.zeros hc, T'.zeros hc]

/-- **Tableaux of shape `μ` form a valued set**: for injective `x`, finitely many tableaux have a
given weight. -/
theorem finiteFibres_ssytWt {x : ℕ → ι} (hx : Function.Injective x) (μ : YoungDiagram) :
    FiniteFibres (ssytWt (μ := μ) x) := by
  intro d
  obtain ⟨B, hB⟩ := (d.support.finite_toSet.preimage hx.injOn).bddAbove
  refine (finite_ssyt_lt μ (B + 1)).subset ?_
  intro T hT i j hc
  have h1 := one_le_ssytWt x T hc
  have hT' : ssytWt x T = d := hT
  rw [hT'] at h1
  have : T i j ∈ x ⁻¹' ↑d.support := by
    simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]
    omega
  exact Nat.lt_succ_of_le (hB this)

/-- **The Schur function** `s_μ(x₀, x₁, …)`: the total weight of all semistandard Young tableaux
of shape `μ`, entries in `ℕ`. -/
noncomputable def schurInf (R : Type*) [CommSemiring R] [TopologicalSpace R] (x : ℕ → ι)
    (μ : YoungDiagram) : MvPowerSeries ι R :=
  ∑' T : SemistandardYoungTableau μ, mono (ssytWt x T)

/-- The variables other than `x_j` and `y_i` for `i, j ≥ M`. -/
def varsLT (x y : ℕ → ι) (M : ℕ) : Set ι := (x '' Set.Ici M ∪ y '' Set.Ici M)ᶜ

theorem mem_varsLT_left {x y : ℕ → ι} (hx : Function.Injective x)
    (hxy : Disjoint (Set.range x) (Set.range y)) (M j : ℕ) : x j ∈ varsLT x y M ↔ j < M := by
  simp only [varsLT, Set.mem_compl_iff, Set.mem_union, Set.mem_image, Set.mem_Ici, not_or,
    not_exists, not_and]
  constructor
  · intro h
    by_contra hj
    exact h.1 j (by omega) rfl
  · intro hj
    refine ⟨fun k hk hxk => ?_, fun k _ hyk => ?_⟩
    · have := hx hxk
      omega
    · exact Set.disjoint_left.mp hxy ⟨j, rfl⟩ ⟨k, hyk⟩

theorem mem_varsLT_right {x y : ℕ → ι} (hy : Function.Injective y)
    (hxy : Disjoint (Set.range x) (Set.range y)) (M i : ℕ) : y i ∈ varsLT x y M ↔ i < M := by
  have : varsLT x y M = varsLT y x M := by
    simp only [varsLT, Set.union_comm]
  rw [this]
  exact mem_varsLT_left hy hxy.symm M i

theorem exists_varsLT {x y : ℕ → ι} (hx : Function.Injective x) (hy : Function.Injective y)
    (e : ι →₀ ℕ) : ∃ M, ↑e.support ⊆ varsLT x y M := by
  obtain ⟨B1, hB1⟩ := (e.support.finite_toSet.preimage hx.injOn).bddAbove
  obtain ⟨B2, hB2⟩ := (e.support.finite_toSet.preimage hy.injOn).bddAbove
  refine ⟨max B1 B2 + 1, fun v hv => ?_⟩
  simp only [varsLT, Set.mem_compl_iff, Set.mem_union, Set.mem_image, Set.mem_Ici, not_or,
    not_exists, not_and]
  constructor
  · intro j hj hxj
    have := hB1 (show j ∈ x ⁻¹' ↑e.support by rw [Set.mem_preimage, hxj]; exact hv)
    omega
  · intro i hi hyi
    have := hB2 (show i ∈ y ⁻¹' ↑e.support by rw [Set.mem_preimage, hyi]; exact hv)
    omega

section Keep

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [T2Space R]

/-- **Killing the variables `x_j` for `j ≥ M`** sends the Schur function to the Schur polynomial
in `x₀, …, x_{M−1}`. -/
theorem keep_schurInf {x : ℕ → ι} (hx : Function.Injective x) {V : Set ι} {M : ℕ}
    (hV : ∀ j, x j ∈ V ↔ j < M) (μ : YoungDiagram) :
    keep V (schurInf R x μ) = schurSSYT R x M μ := by
  classical
  rw [schurInf, keep_tsum (summable_mono (finiteFibres_ssytWt hx μ))]
  simp only [keep_mono]
  have hiff : ∀ T : SemistandardYoungTableau μ,
      ↑(ssytWt x T).support ⊆ V ↔ ∀ i j, (i, j) ∈ μ → T i j < M := by
    intro T
    constructor
    · intro h i j hc
      have h1 := one_le_ssytWt x T hc
      exact (hV _).1 (h (by simp only [Finset.mem_coe, Finsupp.mem_support_iff]; omega))
    · intro h v hv
      obtain ⟨i, j, hc, rfl⟩ := exists_of_mem_support_ssytWt x T hv
      exact (hV _).2 (h i j hc)
  rw [schurSSYT]
  refine Eq.trans ?_ (tsum_subtype {T : SemistandardYoungTableau μ |
    ∀ i j, (i, j) ∈ μ → T i j < M} (fun T => (mono (ssytWt x T) : MvPowerSeries ι R))).symm
  refine tsum_congr (fun T => ?_)
  by_cases h : ∀ i j, (i, j) ∈ μ → T i j < M
  · rw [ite_eq_left ((hiff T).2 h), Set.indicator_of_mem (show T ∈ {T : SemistandardYoungTableau μ |
      ∀ i j, (i, j) ∈ μ → T i j < M} from h)]
  · rw [ite_eq_right (fun h' => h ((hiff T).1 h')), Set.indicator_of_notMem (show T ∉
      {T : SemistandardYoungTableau μ | ∀ i j, (i, j) ∈ μ → T i j < M} from h)]

end Keep

/-! ## Finitely supported matrices -/

/-- The weight of a finitely supported matrix: `Σ_{(i, j)} A (i, j) • (x_j + y_i)`. -/
noncomputable def matWtInf (x y : ℕ → ι) (A : ℕ × ℕ →₀ ℕ) : ι →₀ ℕ :=
  A.sum (fun p a => a • cellWt x y p.1 p.2)

theorem le_matWtInf (x y : ℕ → ι) (A : ℕ × ℕ →₀ ℕ) (p : ℕ × ℕ) :
    A p ≤ matWtInf x y A (x p.2) ∧ A p ≤ matWtInf x y A (y p.1) := by
  classical
  by_cases hp : p ∈ A.support
  · simp only [matWtInf, Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    have key : ∀ v, A p ≤ (A p • cellWt x y p.1 p.2) v → A p ≤ ∑ q ∈ A.support,
        (A q • cellWt x y q.1 q.2) v := fun v hv =>
      le_trans hv (Finset.single_le_sum (f := fun q => (A q • cellWt x y q.1 q.2) v)
        (fun _ _ => Nat.zero_le _) hp)
    refine ⟨key _ ?_, key _ ?_⟩ <;>
      simp only [cellWt, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_eq_same,
        smul_eq_mul] <;> exact Nat.le_mul_of_pos_right _ (by omega)
  · rw [Finsupp.notMem_support_iff.mp hp]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem exists_of_mem_support_matWtInf (x y : ℕ → ι) (A : ℕ × ℕ →₀ ℕ) {v : ι}
    (hv : v ∈ (matWtInf x y A).support) : ∃ p ∈ A.support, v = x p.2 ∨ v = y p.1 := by
  classical
  have := Finsupp.support_finsetSum hv
  simp only [Finset.mem_biUnion] at this
  obtain ⟨p, hp, hv'⟩ := this
  refine ⟨p, hp, ?_⟩
  have := Finsupp.support_smul hv'
  have := Finsupp.support_add this
  simp only [Finset.mem_union] at this
  rcases this with h | h
  · left
    simpa using Finsupp.support_single_subset h
  · right
    simpa using Finsupp.support_single_subset h

/-- **Finitely supported matrices form a valued set**, for injective `x` and `y`. -/
theorem finiteFibres_matWtInf {x y : ℕ → ι} (hx : Function.Injective x)
    (hy : Function.Injective y) : FiniteFibres (matWtInf x y) := by
  classical
  intro d
  obtain ⟨B1, hB1⟩ := (d.support.finite_toSet.preimage hx.injOn).bddAbove
  obtain ⟨B2, hB2⟩ := (d.support.finite_toSet.preimage hy.injOn).bddAbove
  let K := max B1 B2 + 1
  let box : Finset (ℕ × ℕ) := Finset.range K ×ˢ Finset.range K
  have hsupp : ∀ A : ℕ × ℕ →₀ ℕ, matWtInf x y A = d → ∀ p, A p ≠ 0 → p ∈ box := by
    intro A hA p hp
    obtain ⟨h1, h2⟩ := le_matWtInf x y A p
    rw [hA] at h1 h2
    have a1 := hB1 (show p.2 ∈ x ⁻¹' ↑d.support by
      simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]; omega)
    have a2 := hB2 (show p.1 ∈ y ⁻¹' ↑d.support by
      simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]; omega)
    simp only [box, Finset.mem_product, Finset.mem_range]
    omega
  apply Set.Finite.of_finite_image (f := fun A : ℕ × ℕ →₀ ℕ => fun p : box => A p)
  · apply (Set.Finite.pi (t := fun _ : box => Set.Iic (Finsupp.degree d))
      (fun _ => Set.finite_Iic _)).subset
    rintro _ ⟨A, hA, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]
    intro p
    have h1 := (le_matWtInf x y A p).1
    have hA' : matWtInf x y A = d := hA
    rw [hA'] at h1
    exact le_trans h1 (Finsupp.le_degree _ _)
  · intro A hA A' hA' h
    ext p
    by_cases hp : p ∈ box
    · exact congrFun h ⟨p, hp⟩
    · have e1 : A p = 0 := by
        by_contra hne
        exact hp (hsupp A hA p hne)
      have e2 : A' p = 0 := by
        by_contra hne
        exact hp (hsupp A' hA' p hne)
      rw [e1, e2]

/-- Matrices supported in `[0, M)²` are the `M × M` matrices. -/
noncomputable def boxEquiv (M : ℕ) : (Fin M → Fin M → ℕ) ≃
    {A : ℕ × ℕ →₀ ℕ // ∀ p, A p ≠ 0 → p.1 < M ∧ p.2 < M} where
  toFun B := ⟨Finsupp.onFinset (Finset.range M ×ˢ Finset.range M) (fun p => extM B p.1 p.2)
      (fun p hp => by
        simp only [extM] at hp
        split at hp
        · rename_i h
          simpa [Finset.mem_product] using h
        · exact absurd rfl hp),
    fun p hp => by
      simp only [Finsupp.onFinset_apply, extM] at hp
      split at hp
      · assumption
      · exact absurd rfl hp⟩
  invFun A := fun i j => A.1 (i, j)
  left_inv B := by
    funext i j
    simp [extM]
  right_inv A := by
    apply Subtype.ext
    ext p
    simp only [Finsupp.onFinset_apply, extM]
    split
    · rfl
    · rename_i h
      by_contra hne
      exact h (A.2 p (Ne.symm hne))

theorem matWtInf_boxEquiv (x y : ℕ → ι) (M : ℕ) (B : Fin M → Fin M → ℕ) :
    matWtInf x y (boxEquiv M B).1 = matWt x y B := by
  simp only [boxEquiv, Equiv.coe_fn_mk, matWtInf]
  rw [Finsupp.onFinset_sum (g := fun (p : ℕ × ℕ) (a : ℕ) => a • cellWt x y p.1 p.2) _
      (fun _ => zero_smul _ _), Finset.sum_product, matWt,
    Finset.sum_range (fun i => ∑ j ∈ Finset.range M, extM B i j • cellWt x y i j)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_range (fun j => extM B i j • cellWt x y i j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [extM, cellWt]

section KeepMat

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [T2Space R]

/-- **Killing the variables `x_j`, `y_i` for `i, j ≥ M`** sends the total weight of the
finitely supported matrices to that of the `M × M` matrices. -/
theorem keep_tsum_matWtInf {x y : ℕ → ι} (hx : Function.Injective x)
    (hy : Function.Injective y) {V : Set ι} {M : ℕ} (hVx : ∀ j, x j ∈ V ↔ j < M)
    (hVy : ∀ i, y i ∈ V ↔ i < M) :
    keep V (∑' A : ℕ × ℕ →₀ ℕ, (mono (matWtInf x y A) : MvPowerSeries ι R))
      = ∑' B : Fin M → Fin M → ℕ, (mono (matWt x y B) : MvPowerSeries ι R) := by
  classical
  rw [keep_tsum (summable_mono (finiteFibres_matWtInf hx hy))]
  simp only [keep_mono]
  let S : Set (ℕ × ℕ →₀ ℕ) := {A | ∀ p, A p ≠ 0 → p.1 < M ∧ p.2 < M}
  have hiff : ∀ A, ↑(matWtInf x y A).support ⊆ V ↔ A ∈ S := by
    intro A
    constructor
    · intro h p hp
      obtain ⟨h1, h2⟩ := le_matWtInf x y A p
      exact ⟨(hVy _).1 (h (by simp only [Finset.mem_coe, Finsupp.mem_support_iff]; omega)),
        (hVx _).1 (h (by simp only [Finset.mem_coe, Finsupp.mem_support_iff]; omega))⟩
    · intro h v hv
      obtain ⟨p, hp, hpv⟩ := exists_of_mem_support_matWtInf x y A hv
      have hp' := h p (Finsupp.mem_support_iff.mp hp)
      rcases hpv with rfl | rfl
      · exact (hVx _).2 hp'.2
      · exact (hVy _).2 hp'.1
  have e1 : ∑' A : ℕ × ℕ →₀ ℕ, (if ↑(matWtInf x y A).support ⊆ V then mono (matWtInf x y A)
      else 0 : MvPowerSeries ι R) = ∑' A : S, (mono (matWtInf x y A.1) : MvPowerSeries ι R) := by
    rw [tsum_subtype S (fun A => (mono (matWtInf x y A) : MvPowerSeries ι R))]
    refine tsum_congr (fun A => ?_)
    by_cases h : A ∈ S
    · rw [ite_eq_left ((hiff A).2 h), Set.indicator_of_mem h]
    · rw [ite_eq_right (fun h' => h ((hiff A).1 h')), Set.indicator_of_notMem h]
  rw [e1]
  refine Eq.trans (((boxEquiv M : (Fin M → Fin M → ℕ) ≃ S)).tsum_eq
    (fun A : S => (mono (matWtInf x y A.1) : MvPowerSeries ι R))).symm ?_
  refine tsum_congr (fun B => ?_)
  rw [show ((boxEquiv M : (Fin M → Fin M → ℕ) ≃ S) B).1 = (boxEquiv M B).1 from rfl,
    matWtInf_boxEquiv]

end KeepMat

/-! ## Summability over Young diagrams -/

theorem lt_card_of_mem {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∈ μ) :
    i < μ.cells.card ∧ j < μ.cells.card := by
  constructor
  · have hsub : (Finset.range (i + 1)).map ⟨fun r => (r, 0), fun a b h => by simpa using h⟩
        ⊆ μ.cells := by
      intro c hc
      simp only [Finset.mem_map, Finset.mem_range] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      exact μ.up_left_mem (by omega) (Nat.zero_le _) h
    have := Finset.card_le_card hsub
    simp only [Finset.card_map, Finset.card_range] at this
    omega
  · have hsub : (Finset.range (j + 1)).map ⟨fun c => (0, c), fun a b h => by simpa using h⟩
        ⊆ μ.cells := by
      intro c hc
      simp only [Finset.mem_map, Finset.mem_range] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      exact μ.up_left_mem (Nat.zero_le _) (by omega) h
    have := Finset.card_le_card hsub
    simp only [Finset.card_map, Finset.card_range] at this
    omega

/-- Young diagrams with at most `k` cells are finitely many. -/
theorem finite_youngDiagram_card_le (k : ℕ) : {μ : YoungDiagram | μ.cells.card ≤ k}.Finite := by
  apply Set.Finite.of_finite_image (f := fun μ : YoungDiagram => μ.cells)
  · apply (Finset.powerset (Finset.range k ×ˢ Finset.range k)).finite_toSet.subset
    rintro _ ⟨μ, hμ, rfl⟩
    refine Finset.mem_coe.mpr (Finset.mem_powerset.mpr ?_)
    intro c hc
    have := lt_card_of_mem (μ := μ) (i := c.1) (j := c.2) hc
    have hμ' : μ.cells.card ≤ k := hμ
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · intro μ _ ν _ h
    exact YoungDiagram.ext h

section Main

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [T3Space R]

omit [IsTopologicalSemiring R] in
/-- **The family `μ ↦ s_μ(x) s_μ(y)` is summable**: only finitely many diagrams contribute to
each coefficient. -/
theorem summable_schurInf_mul {x y : ℕ → ι} (hx : Function.Injective x) :
    Summable (fun μ : YoungDiagram => schurInf R x μ * schurInf R y μ) := by
  classical
  rw [WithPiTopology.summable_iff_summable_coeff]
  intro e
  apply summable_of_hasFiniteSupport
  refine (finite_youngDiagram_card_le (Finsupp.degree e)).subset ?_
  intro μ hμ
  simp only [Function.mem_support] at hμ
  rw [coeff_mul] at hμ
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  have h1 : coeff p.1 (schurInf R x μ) ≠ 0 := left_ne_zero_of_mul hne
  rw [schurInf, coeff_tsum_mono (finiteFibres_ssytWt hx μ)] at h1
  have hne' : ((finiteFibres_ssytWt hx μ p.1).toFinset).Nonempty := by
    rw [← Finset.ne_empty_iff_nonempty]
    intro h
    apply h1
    rw [h]
    simp
  obtain ⟨T, hT⟩ := hne'
  rw [Set.Finite.mem_toFinset] at hT
  have hT' : ssytWt x T = p.1 := hT
  show μ.cells.card ≤ Finsupp.degree e
  rw [← degree_ssytWt x T, hT']
  rw [Finset.mem_antidiagonal] at hp
  exact Finsupp.degree_mono (by rw [← hp]; exact le_self_add)

/-- **The Cauchy identity in infinitely many variables.** For injective families of variables
`x y : ℕ → ι` with disjoint ranges, in `MvPowerSeries ι R` with the product topology,

  `∑' μ, s_μ(x₀, x₁, …) s_μ(y₀, y₁, …) = ∑' A, ∏_{i,j} (x_j y_i) ^ (A (i, j))`,

the sum on the left over all Young diagrams, `s_μ` the total weight of all semistandard Young
tableaux of shape `μ` (Mathlib's `SemistandardYoungTableau`), the sum on the right over all
finitely supported `A : ℕ × ℕ →₀ ℕ`. Both families are summable (`summable_schurInf_mul`,
`finiteFibres_matWtInf`). -/
@[frame_pattern]
theorem cauchy_inf {x y : ℕ → ι} (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : Disjoint (Set.range x) (Set.range y)) :
    ∑' μ : YoungDiagram, schurInf R x μ * schurInf R y μ
      = ∑' A : ℕ × ℕ →₀ ℕ, (mono (matWtInf x y A) : MvPowerSeries ι R) := by
  ext e
  obtain ⟨M, hM⟩ := exists_varsLT hx hy e
  rw [← coeff_keep_of_subset _ _ hM,
    ← coeff_keep_of_subset _ (∑' A : ℕ × ℕ →₀ ℕ, (mono (matWtInf x y A) : MvPowerSeries ι R)) hM]
  congr 1
  rw [keep_tsum (summable_schurInf_mul hx),
    keep_tsum_matWtInf hx hy (mem_varsLT_left hx hxy M) (mem_varsLT_right hy hxy M),
    ← cauchy_ssyt (m := M) (n := M) x y]
  refine tsum_congr (fun μ => ?_)
  rw [keep_mul, keep_schurInf hx (mem_varsLT_left hx hxy M),
    keep_schurInf hy (mem_varsLT_right hy hxy M)]

end Main

end Inf

end RMT.Symmetric
