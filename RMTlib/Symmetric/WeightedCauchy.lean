import RMTlib.Symmetric.SSYT
import RMTlib.Tableaux.HookContent
import MeaningLib.Frame.Pattern

/-!
# The Cauchy identity weighted by shape, and content products

RSK (`rskEquiv`) preserves the common shape of the two tableaux. So any weight `w(λ)` on shapes
can be carried along the bijection, and the Cauchy identity holds with it, for every `w`:

  `∑' λ, w(λ) s_λ(x) s_λ(y) = ∑' A, w(shape (RSK A)) ∏_{i,j} (x_j y_i) ^ (A i j)`

(`cauchy_weighted`). The unweighted identity is `w = 1`. A closed product on the right exists
only for special weights; `w(λ) = T^{|λ|}` is one, since `|shape (RSK A)| = Σ A` (`size_rskShape`),
and it gives the graded identity used at the finite places (`cauchy_graded`).

The weights of interest are **content products**. The content of the cell `(i, j)` (row `i`,
column `j`) is `j − i`, and

  `contentProd f μ = ∏_{(i, j) ∈ μ} f (j − i)`.

They are the form in which the places of the programme meet:
* `f = T` (constant) gives `T^{|λ|}`, the finite-place weight (`contentProd_const`);
* `f c = N + c` gives the hook-content product `∏ (N + c − i) = s_λ(1^N) · H(λ)` that twists the
  Fock pairing (`RMT.fischer_trX_pow_eq_twisted_hall`). It vanishes exactly on the diagrams with
  more than `N` rows (`contentProd_nat_add_eq_zero_iff`): its support is the cut that Schur
  orthogonality on `U(N)` imposes.

**Conjugation negates contents.** Transposing a diagram swaps the coordinates of its cells, so it
sends the content `c` to `−c`: `contentProd f μᵀ = contentProd (f ∘ neg) μ`
(`contentProd_transpose`). The two cuts `∏ (N + c)` (at most `N` rows) and `∏ (N − c)` (at most
`N` columns, the dual side of Bump–Gamburd) are exchanged by it
(`contentProd_nat_sub_eq_zero_iff`). Content weights therefore carry the diagonal symmetry with
them, unlike weights written in terms of row lengths.

Content products are defined on Mathlib's `YoungDiagram`, where cells and transposition are
native. `contentProdP` is the same product on the padded shapes `Part` of the growth diagram, and
`contentProdP_rowsOf` identifies the two.

## Main results

* `summable_smul_mono`: rescaling a valued set by any coefficients keeps it summable.
* `cauchy_weighted`: the Cauchy identity with an arbitrary shape weight.
* `size_rskShape`, `cauchy_graded`: the case `w = T^{|λ|}`.
* `contentProd_transpose`, `contentProd_const`, `contentProd_eq_zero_iff`,
  `contentProd_nat_add_eq_zero_iff`, `contentProd_nat_sub_eq_zero_iff`.
* `contentProdP_rowsOf`, `cauchy_content`: the Cauchy identity weighted by a content product.
* `contentProdP_nat_add_eq`: `∏ (N + c) = s_λ(1^N) · H(λ)`, the Fock twist, by the hook-content
  formula.
-/

open scoped MvPowerSeries.WithPiTopology
open MvPowerSeries

namespace RMT.Symmetric

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthGeneric (grow)
open RMT.RSK.GrowthSuper (size colSum)
open RMT.RSK.GrowthBij

/-! ## Rescaled valued sets -/

section Summable

variable {A ι R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- **Rescaling a valued set keeps it summable**: each coefficient still has finite support. -/
theorem summable_smul_mono {w : A → ι →₀ ℕ} (hw : FiniteFibres w) (c : A → R) :
    Summable (fun a => c a • (mono (w a) : MvPowerSeries ι R)) := by
  rw [WithPiTopology.summable_iff_summable_coeff]
  intro d
  refine summable_of_hasFiniteSupport ((hw d).subset ?_)
  intro a ha
  apply support_coeff_mono_subset (R := R) w d
  intro h
  have h' : coeff d (mono (w a) : MvPowerSeries ι R) = 0 := h
  apply ha
  simp only [MvPowerSeries.coeff_smul]
  rw [h', mul_zero]

end Summable

/-! ## The Cauchy identity with a shape weight -/

variable {N n m : ℕ}

/-- The common shape of the two tableaux that RSK assigns to a matrix. -/
def rskShape (N : ℕ) (A : Fin n → Fin m → ℕ) : Part := (rskFwd (N := N) A).1.1.shape

section Weighted

variable {ι R : Type*} [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
  [T3Space R]

/-- **The Cauchy identity with an arbitrary shape weight** `w`:

  `∑' λ, w(λ) s_λ(x) s_λ(y) = ∑' A, w(shape (RSK A)) ∏_{i,j} (x_j y_i) ^ (A i j)`,

in `MvPowerSeries ι R` with the product topology, for shapes padded to `N ≥ m` rows. RSK preserves
the shape, so the weight is carried along `rskEquiv` exactly as the monomials are in `cauchy`. -/
@[frame_pattern]
theorem cauchy_weighted (x y : ℕ → ι) (hm : m ≤ N) (w : Part → R) :
    ∑' lam : Part, w lam • (schur R x N m lam * schur R y N n lam)
      = ∑' A : Fin n → Fin m → ℕ,
          w (rskShape N A) • (mono (matWt x y A) : MvPowerSeries ι R) := by
  have : T3Space (MvPowerSeries ι R) := inferInstanceAs (T3Space ((ι →₀ ℕ) → R))
  let F : Pairs N n m → MvPowerSeries ι R := fun pq => w pq.1.1.shape • mono (pq.wt x y)
  have hF : ∀ A : Fin n → Fin m → ℕ,
      F (rskEquiv hm A) = w (rskShape N A) • (mono (matWt x y A) : MvPowerSeries ι R) := by
    intro A
    simp only [F, wt_rskEquiv]
    rfl
  have h1 : ∑' A : Fin n → Fin m → ℕ, w (rskShape N A) • (mono (matWt x y A) : MvPowerSeries ι R)
      = ∑' pq, F pq := by
    rw [← (rskEquiv hm).tsum_eq]
    exact tsum_congr (fun A => (hF A).symm)
  have hsF : Summable F := by
    rw [← (rskEquiv hm).summable_iff]
    convert summable_smul_mono (R := R) (finiteFibres_matWt (n := n) (m := m) x y)
      (fun A => w (rskShape N A)) using 1
    funext A
    exact hF A
  have hs : Summable (F ∘ (pairsSigma (N := N) (n := n) (m := m)).symm) :=
    (pairsSigma (N := N) (n := n) (m := m)).symm.summable_iff.mpr hsF
  rw [h1, ← (pairsSigma (N := N) (n := n) (m := m)).symm.tsum_eq F]
  refine Eq.trans ?_ (Summable.tsum_sigma' (fun _ => Summable.of_finite) hs).symm
  refine tsum_congr (fun lam => ?_)
  have := Fintype.ofFinite {T : Tab N m // T.shape = lam}
  have := Fintype.ofFinite {T : Tab N n // T.shape = lam}
  rw [schur_mul_schur x y lam, tsum_fintype, tsum_fintype, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [Function.comp_apply, F]
  rw [show (pairsSigma.symm ⟨lam, c⟩ : Pairs N n m).1.1.shape = lam from c.1.2]

end Weighted

/-! ## The graded case: `w = T^{|λ|}` -/

theorem size_zeros : ∀ N, size (zeros N) = 0
  | 0 => rfl
  | N + 1 => by
    rw [zeros, List.replicate_succ, RMT.RSK.GrowthSuper.size_cons, Nat.zero_add]
    exact size_zeros N

/-- **The RSK shape has as many boxes as the matrix has entries, counted with multiplicity.** -/
theorem size_rskShape (hm : m ≤ N) (A : Fin n → Fin m → ℕ) :
    size (rskShape N A) = ∑ i : Fin n, ∑ j : Fin m, A i j := by
  have key : ∀ k, k ≤ m → size (grow Fb (zeros N) (extM A) n k)
      = ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range n, extM A i j := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [RMT.RSK.GrowthGeneric.grow_zero_right, size_zeros, Finset.sum_range_zero]
    | succ k ih =>
      intro hk
      rw [size_top_succ (extM A) N n m hm k (by omega), ih (by omega), Finset.sum_range_succ,
        colSum_eq]
  have hsh : rskShape N A = grow Fb (zeros N) (extM A) n m := by
    simp [rskShape, rskFwd, Tab.shape, Tab.mk', freeze]
  rw [hsh, key m (Nat.le_refl _), Finset.sum_comm,
    Finset.sum_range (fun i => ∑ j ∈ Finset.range m, extM A i j)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_range (fun j => extM A i j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [extM]

/-- **The graded Cauchy identity**: weighting by `T^{|λ|}` weights each matrix by `T^{Σ A}`:

  `∑' λ, T^{|λ|} s_λ(x) s_λ(y) = ∑' A, T^{Σ A} ∏_{i,j} (x_j y_i) ^ (A i j)`.

This is the form specialised at the finite places, `T = q^{−s}`. -/
@[frame_pattern]
theorem cauchy_graded {ι R : Type*} [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] [T3Space R] (x y : ℕ → ι) (hm : m ≤ N) (T : R) :
    ∑' lam : Part, T ^ size lam • (schur R x N m lam * schur R y N n lam)
      = ∑' A : Fin n → Fin m → ℕ,
          T ^ (∑ i, ∑ j, A i j) • (mono (matWt x y A) : MvPowerSeries ι R) := by
  rw [cauchy_weighted x y hm (fun lam => T ^ size lam)]
  exact tsum_congr (fun A => by rw [size_rskShape hm A])

/-! ## Content products -/

section Content

/-- The content `j − i` of the cell `(i, j)` (row `i`, column `j`). -/
def content (c : ℕ × ℕ) : ℤ := (c.2 : ℤ) - c.1

theorem content_swap (c : ℕ × ℕ) : content c.swap = -content c := by
  simp [content]

variable {R : Type*} [CommMonoid R]

/-- **The content product** `∏_{(i, j) ∈ μ} f (j − i)`. Symmetric under conjugation up to
negating contents (`contentProd_transpose`). -/
def contentProd (f : ℤ → R) (μ : YoungDiagram) : R := ∏ c ∈ μ.cells, f (content c)

/-- **Conjugation negates contents**: `contentProd f μᵀ = contentProd (f ∘ neg) μ`. -/
theorem contentProd_transpose (f : ℤ → R) (μ : YoungDiagram) :
    contentProd f μ.transpose = contentProd (fun z => f (-z)) μ := by
  unfold contentProd
  refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simpa [YoungDiagram.mem_cells, YoungDiagram.mem_transpose] using hc
  · intro c hc
    simpa [YoungDiagram.mem_cells, YoungDiagram.mem_transpose] using hc
  · intro c _
    simp
  · intro c _
    simp
  · intro c _
    rw [content_swap]
    simp

/-- A constant content weight counts boxes: `contentProd (fun _ => T) μ = T^{|μ|}`. -/
theorem contentProd_const (T : R) (μ : YoungDiagram) :
    contentProd (fun _ => T) μ = T ^ μ.cells.card := by
  simp [contentProd]

theorem contentProd_mul (f g : ℤ → R) (μ : YoungDiagram) :
    contentProd (fun z => f z * g z) μ = contentProd f μ * contentProd g μ := by
  simp [contentProd, Finset.prod_mul_distrib]

end Content

section Zero

variable {R : Type*} [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]

/-- A content product vanishes exactly when some content is a zero of `f`. -/
theorem contentProd_eq_zero_iff (f : ℤ → R) (μ : YoungDiagram) :
    contentProd f μ = 0 ↔ ∃ c ∈ μ, f (content c) = 0 := by
  simp [contentProd, Finset.prod_eq_zero_iff]

end Zero

/-- **The hook-content product `∏ (N + c)` vanishes exactly on the diagrams with more than `N`
rows**, that is when the cell `(N, 0)` is in `μ`. Its support is the cut `ℓ(λ) ≤ N`. -/
theorem contentProd_nat_add_eq_zero_iff (N : ℕ) (μ : YoungDiagram) :
    contentProd (fun z : ℤ => (N : ℤ) + z) μ = 0 ↔ (N, 0) ∈ μ := by
  rw [contentProd_eq_zero_iff]
  constructor
  · rintro ⟨⟨i, j⟩, hc, h⟩
    simp only [content] at h
    exact μ.up_left_mem (by omega) (Nat.zero_le _) hc
  · intro h
    exact ⟨(N, 0), h, by simp [content]⟩

/-- **The dual cut**: `∏ (N − c)` vanishes exactly on the diagrams with more than `N` columns.
It is the transpose of `contentProd_nat_add_eq_zero_iff`. -/
theorem contentProd_nat_sub_eq_zero_iff (N : ℕ) (μ : YoungDiagram) :
    contentProd (fun z : ℤ => (N : ℤ) - z) μ = 0 ↔ (0, N) ∈ μ := by
  have h := contentProd_transpose (fun z : ℤ => (N : ℤ) + z) μ
  simp only [← sub_eq_add_neg] at h
  rw [← h, contentProd_nat_add_eq_zero_iff, YoungDiagram.mem_transpose]
  rfl

/-! ## Content products on padded shapes -/

section Padded

variable {R : Type*} [CommMonoid R]

/-- The content product on a padded shape: `∏_{i} ∏_{j < λ_i} f (j − i)`. -/
def contentProdP (f : ℤ → R) (lam : Part) : R :=
  ∏ i ∈ Finset.range lam.length, ∏ j ∈ Finset.range (lam.getD i 0), f ((j : ℤ) - i)

/-- **The two content products agree** on a diagram with at most `N` rows. -/
theorem contentProdP_rowsOf {N : ℕ} {μ : YoungDiagram} (hμ : RowsLE N μ) (f : ℤ → R) :
    contentProdP f (rowsOf N μ) = contentProd f μ := by
  rw [contentProd, Finset.prod_finset_product μ.cells (Finset.range N)
    (fun r => Finset.range (μ.rowLen r)) (fun ⟨r, col⟩ => by
    rw [YoungDiagram.mem_cells, mem_iff_of_rowsLE hμ, Finset.mem_range, Finset.mem_range]),
    contentProdP, length_rowsOf]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [getD_rowsOf, if_pos (Finset.mem_range.mp hi)]
  rfl

theorem contentProdP_const (T : R) (lam : Part) :
    contentProdP (fun _ => T) lam = T ^ size lam := by
  induction lam with
  | nil => simp [contentProdP, RMT.RSK.GrowthSuper.size]
  | cons a l ih =>
    rw [RMT.RSK.GrowthSuper.size_cons, pow_add, ← ih]
    simp only [contentProdP, Finset.prod_const, Finset.card_range, List.length_cons]
    rw [Finset.prod_range_succ', mul_comm]
    simp

/-- On a shape with `N` rows, `∏ (N + c)` is the product `∏ (N − i + j)` of the hook-content
formula. -/
theorem contentProdP_nat_add_ofFn {N : ℕ} (ν : Fin N → ℕ) :
    contentProdP (fun z : ℤ => (N : ℤ) + z) (List.ofFn ν)
      = ∏ i : Fin N, ∏ c ∈ Finset.range (ν i), ((N - i + c : ℕ) : ℤ) := by
  rw [contentProdP, List.length_ofFn,
    Finset.prod_range (fun i => ∏ j ∈ Finset.range ((List.ofFn ν).getD i 0),
      ((N : ℤ) + ((j : ℤ) - i)))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hg : (List.ofFn ν).getD i 0 = ν i := by simp [List.getD_eq_getElem?_getD]
  rw [hg]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [Nat.cast_add, Nat.cast_sub i.2.le]
  ring

/-- **`∏ (N + c)` is `s_λ(1^N) · H(λ)`**, the number of semistandard tableaux with entries
`≤ N` times the hook product: the hook-content formula (`RMT.hook_content_formula`). This is the
twist of the Fock pairing on class functions. -/
theorem contentProdP_nat_add_eq {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) :
    contentProdP (fun z : ℤ => (N : ℤ) + z) (List.ofFn ν) = ((gtCount N ν * hookProd ν : ℕ) : ℤ) := by
  rw [contentProdP_nat_add_ofFn, hook_content_formula N ν hν]
  push_cast [Nat.cast_prod]
  rfl

end Padded

/-- **The Cauchy identity weighted by a content product**:

  `∑' λ, (∏_{(i,j) ∈ λ} f (j − i)) s_λ(x) s_λ(y)
     = ∑' A, (∏_{(i,j) ∈ shape (RSK A)} f (j − i)) ∏ (x_j y_i) ^ (A i j)`. -/
@[frame_pattern]
theorem cauchy_content {ι R : Type*} [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] [T3Space R] (x y : ℕ → ι) (hm : m ≤ N) (f : ℤ → R) :
    ∑' lam : Part, contentProdP f lam • (schur R x N m lam * schur R y N n lam)
      = ∑' A : Fin n → Fin m → ℕ,
          contentProdP f (rskShape N A) • (mono (matWt x y A) : MvPowerSeries ι R) :=
  cauchy_weighted x y hm (contentProdP f)

end RMT.Symmetric
