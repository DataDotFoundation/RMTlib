import RMTlib.Symmetric.JacobiTrudi
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.ComputeDegree

/-!
# The bialternant formula and the dual Pieri rule

For values `a : ℕ → R` in a commutative ring, the alternant of an exponent vector
`μ : Fin n → ℕ` is `altV a n μ = det (a_i ^ μ_j)_{i, j < n}`, and `δ = stair n`,
`δ_j = n − 1 − j`. This file proves, over any commutative ring:

* `altV_add_stair` (**bialternant formula**, Jacobi–Trudi form): for every `l : Fin n → ℕ`,
  `a_{l+δ} = a_δ · det (h_{l_i − i + j}(a₀, …, a_{n−1}))`;
* `altV_add_stair_eq_mul_schurV`: for antitone `l`, `a_{l+δ} = a_δ · s_l(a₀, …, a_{n−1})`,
  with `s_l` the tableau Schur polynomial `schurV` (by `schurV_eq_det`);
* `esymm_mul_schurV` (**dual Pieri rule**): for antitone `l`,
  `e_k · s_l = Σ_J s_{l + 1_J}`, the sum over the `k`-subsets `J ⊆ [n]` with `l + 1_J` antitone,
  i.e. over the ways of adding a vertical strip of `k` boxes, at most one per row.

## Proof

*Bialternant.* With `H(X) = Σ_k h_k X^k = ∏_i (1 − a_i X)⁻¹` (`hSeries_mul_prod`) and
`Q_i(X) = ∏_{i' ≠ i} (1 − a_{i'} X)`, a polynomial of degree `< n`, `H · Q_i = (1 − a_i X)⁻¹`
(`hSeries_mul_Q`), so `a_i ^ p = Σ_{r < n} [X^r] Q_i · h_{p − r}` for every `p ≥ 0`. Hence the
alternant factors as a matrix product `(a_i ^ (l_j + δ_j)) = C · J_lᵀ` with `C` independent of
`l` and `J_l` the Jacobi–Trudi matrix (`alt_eq_mul`), and taking `l = 0` (`J_0` unitriangular)
identifies `det C = a_δ`. This is the classical argument (Macdonald I.3), with no division: it
holds over any commutative ring, for all `l`, antitone or not.

*Dual Pieri.* `e_k · a_μ = Σ_{|J| = k} a_{μ + 1_J}` by expanding the determinant
(`esymm_mul_altV`). For antitone `l`, the terms with `l + 1_J` not antitone have two equal
exponents in `l + 1_J + δ` and vanish. Dividing by `a_δ` in `ℤ[x₀, …, x_{n−1}]` (a Vandermonde
determinant, a non-zero-divisor) gives the rule for the generic point, and evaluation gives it
everywhere (`map_schurV`, `schurV_congr`).

The RH formalisation proves its dual Pieri rule (`GlobalTheory.JSW.esymm_mul_schur`) along the
same lines, through its own bialternant; the bridge `RMTlibBridge.JacobiTrudi` derives its
statement from `esymm_mul_schurV` instead.

## Main results

* `map_hE`, `map_schurV`, `hE_congr`, `schurV_congr`: functoriality in the values.
* `altV_add_stair`, `altV_add_stair_eq_mul_schurV`: the bialternant formula.
* `esymm_mul_altV`: `e_k · a_μ = Σ_{|J| = k} a_{μ + 1_J}`.
* `esymm_mul_schurV`: the dual Pieri rule.
-/

open Finset Matrix

namespace RMT.Symmetric

/-! ## Functoriality -/

section Functorial

variable {R S : Type*} [CommRing R] [CommRing S] {N : ℕ}

/-- `h_k(a₀, …, a_{m−1})` depends only on `a₀, …, a_{m−1}`. -/
theorem hE_congr {a b : ℕ → R} : ∀ {m : ℕ}, (∀ i < m, a i = b i) → ∀ k, hE a m k = hE b m k
  | 0, _, _ => rfl
  | m + 1, h, k => by
    simp only [hE]
    rw [h m (Nat.lt_succ_self m)]
    exact sum_congr rfl fun r _ => by rw [hE_congr (fun i hi => h i (by omega))]

/-- Ring homomorphisms commute with `h_k`. -/
theorem map_hE (f : R →+* S) (a : ℕ → R) : ∀ (m : ℕ) (k : ℤ), f (hE a m k) = hE (f ∘ a) m k
  | 0, k => by simp only [hE]; split_ifs <;> simp
  | m + 1, k => by simp only [hE, map_sum, map_mul, map_pow, Function.comp, map_hE f a m]

/-- Ring homomorphisms commute with the Jacobi–Trudi determinant. -/
theorem map_det_jtMat (f : R →+* S) (a : ℕ → R) (m : ℕ) (l : Fin N → ℕ) :
    f (det (jtMat a m l)) = det (jtMat (f ∘ a) m l) := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [jtMat, map_hE]

/-- The Jacobi–Trudi matrix in `m` variables depends only on `a₀, …, a_{m−1}`. -/
theorem jtMat_congr {a b : ℕ → R} {m : ℕ} (h : ∀ i < m, a i = b i) (l : Fin N → ℕ) :
    jtMat a m l = jtMat b m l := by
  ext i j
  simp only [jtMat, of_apply, hE_congr h]

/-- `s_l(a₀, …, a_{m−1})` depends only on `a₀, …, a_{m−1}`. -/
theorem schurV_congr {a b : ℕ → R} {m : ℕ} (h : ∀ i < m, a i = b i) (l : Fin N → ℕ) :
    schurV a N m l = schurV b N m l := by
  refine sum_congr rfl fun T _ => ?_
  rw [evalMono_wt, evalMono_wt]
  exact prod_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

/-- Ring homomorphisms commute with the evaluated Schur polynomial. -/
theorem map_schurV (f : R →+* S) (a : ℕ → R) (m : ℕ) (l : Fin N → ℕ) :
    f (schurV a N m l) = schurV (f ∘ a) N m l := by
  simp only [schurV, map_sum, evalMono_wt, map_prod, map_pow, Function.comp]

end Functorial

/-! ## The generating series of `h` -/

section Series

variable {R : Type*} [CommRing R]

open PowerSeries

/-- `h_0 = 1`. -/
theorem hE_zero_index (a : ℕ → R) : ∀ m, hE a m 0 = 1
  | 0 => by simp [hE]
  | m + 1 => by simp [hE, hE_zero_index a m]

/-- `H(X) = Σ_k h_k(a₀, …, a_{m−1}) X^k`. -/
noncomputable def hSeries (a : ℕ → R) (m : ℕ) : PowerSeries R := mk fun k => hE a m k

/-- `Σ_r c^r X^r`. -/
noncomputable def geomSeries (c : R) : PowerSeries R := mk fun r => c ^ r

/-- `(Σ_r c^r X^r) (1 − c X) = 1`. -/
theorem geomSeries_mul (c : R) : geomSeries c * (1 - C c * X) = 1 := by
  ext k
  rw [mul_sub, mul_one, map_sub, coeff_one, mul_comm, mul_assoc, coeff_C_mul]
  rcases k with _ | k
  · simp [geomSeries]
  · rw [coeff_succ_X_mul]
    simp [geomSeries, pow_succ']

/-- Adding a variable multiplies `H` by `Σ_r a_m^r X^r`. -/
theorem hSeries_succ (a : ℕ → R) (m : ℕ) :
    hSeries a (m + 1) = geomSeries (a m) * hSeries a m := by
  ext k
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [hSeries, geomSeries, coeff_mk, hE, Int.toNat_natCast]
  refine sum_congr rfl fun r hr => ?_
  rw [Nat.cast_sub (by have := mem_range.mp hr; omega)]

/-- `H(X) · ∏_{i<m} (1 − a_i X) = 1`. -/
theorem hSeries_mul_prod (a : ℕ → R) :
    ∀ m, hSeries a m * ∏ i ∈ range m, (1 - C (a i) * X) = 1
  | 0 => by
    ext k
    simp [hSeries, hE, coeff_one]
  | m + 1 => by
    rw [hSeries_succ, prod_range_succ]
    calc _ = (geomSeries (a m) * (1 - C (a m) * X)) * (hSeries a m * ∏ i ∈ range m,
          (1 - C (a i) * X)) := by ring
      _ = 1 := by rw [geomSeries_mul, hSeries_mul_prod a m, one_mul]

/-- `Q_i(X) = ∏_{i' < n, i' ≠ i} (1 − a_{i'} X)`. -/
noncomputable def Qpoly (a : ℕ → R) (n i : ℕ) : Polynomial R :=
  ∏ i' ∈ (range n).erase i, (1 - Polynomial.C (a i') * Polynomial.X)

/-- `H · Q_i = (1 − a_i X)⁻¹`. -/
theorem hSeries_mul_Q (a : ℕ → R) {n i : ℕ} (hi : i < n) :
    hSeries a n * (Qpoly a n i : PowerSeries R) = geomSeries (a i) := by
  have hQ : (Qpoly a n i : PowerSeries R) = ∏ i' ∈ (range n).erase i, (1 - C (a i') * X) := by
    rw [Qpoly, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp
  have hP : ∏ i' ∈ range n, (1 - C (a i') * X) = (1 - C (a i) * X) * (Qpoly a n i : PowerSeries R) := by
    rw [hQ]
    exact (mul_prod_erase (range n) (fun i' => 1 - C (a i') * X) (mem_range.mpr hi)).symm
  calc hSeries a n * (Qpoly a n i : PowerSeries R)
      = hSeries a n * (Qpoly a n i : PowerSeries R) * (geomSeries (a i) * (1 - C (a i) * X)) := by
        rw [geomSeries_mul, mul_one]
    _ = (hSeries a n * ∏ i' ∈ range n, (1 - C (a i') * X)) * geomSeries (a i) := by rw [hP]; ring
    _ = geomSeries (a i) := by rw [hSeries_mul_prod, one_mul]

/-- `Q_i` has degree `< n`. -/
theorem coeff_Qpoly_eq_zero (a : ℕ → R) {n i r : ℕ} (hi : i < n) (hr : n ≤ r) :
    (Qpoly a n i).coeff r = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have h1 : ∀ i' ∈ (range n).erase i, (1 - Polynomial.C (a i') * Polynomial.X).natDegree ≤ 1 :=
    fun _ _ => by compute_degree
  have := (Polynomial.natDegree_prod_le ((range n).erase i) _).trans (sum_le_sum h1)
  rw [sum_const, card_erase_of_mem (mem_range.mpr hi), card_range, smul_eq_mul, mul_one] at this
  unfold Qpoly
  omega

/-- **The `e`/`h` relation**: `a_i ^ p = Σ_{r < n} [X^r] Q_i · h_{p − r}(a₀, …, a_{n−1})`. -/
theorem sum_coeff_Q_mul_hE (a : ℕ → R) {n i : ℕ} (hi : i < n) (p : ℕ) :
    ∑ r ∈ range n, (Qpoly a n i).coeff r * hE a n ((p : ℤ) - r) = a i ^ p := by
  have h := congrArg (coeff p) (hSeries_mul_Q a hi)
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [hSeries, geomSeries, coeff_mk, Polynomial.coeff_coe] at h
  rw [← h]
  have e1 : ∑ r ∈ range n, (Qpoly a n i).coeff r * hE a n ((p : ℤ) - r)
      = ∑ r ∈ range (n + p + 1), (Qpoly a n i).coeff r * hE a n ((p : ℤ) - r) :=
    sum_subset (fun r hr => by simp at hr ⊢; omega) fun r hr hr' => by
      simp at hr hr'; rw [coeff_Qpoly_eq_zero a hi hr', zero_mul]
  have e2 : ∑ r ∈ range (p + 1), (Qpoly a n i).coeff r * hE a n ((p - r : ℕ) : ℤ)
      = ∑ r ∈ range (n + p + 1), (Qpoly a n i).coeff r * hE a n ((p : ℤ) - r) := by
    rw [sum_congr rfl fun r hr => by
      rw [Nat.cast_sub (by have := mem_range.mp hr; omega)]]
    exact sum_subset (fun r hr => by simp at hr ⊢; omega) fun r hr hr' => by
      simp at hr hr'; rw [hE_neg a n (by omega), mul_zero]
  rw [e1, ← e2]

end Series

/-! ## The bialternant formula -/

section Bialternant

variable {R : Type*} [CommRing R]

/-- The alternant `a_μ(a₀, …, a_{n−1}) = det (a_i ^ μ_j)_{i, j < n}`. -/
noncomputable def altV (a : ℕ → R) (n : ℕ) (μ : Fin n → ℕ) : R :=
  det (of fun i j : Fin n => a i ^ μ j)

/-- The staircase `δ_j = n − 1 − j`. -/
def stair (n : ℕ) : Fin n → ℕ := fun j => n - 1 - j

/-- The matrix `C_{i k} = [X^{n−1−k}] Q_i` of the factorisation `a_{l+δ} = C · J_lᵀ`. -/
noncomputable def cMat (a : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  of fun i k => (Qpoly a n i).coeff (n - 1 - k)

/-- The alternant matrix of `l + δ` is `C · J_lᵀ`, `J_l` the Jacobi–Trudi matrix. -/
theorem alt_eq_mul (a : ℕ → R) (n : ℕ) (l : Fin n → ℕ) :
    (of fun i j : Fin n => a i ^ (l + stair n) j) = cMat a n * (jtMat a n l)ᵀ := by
  ext i j
  rw [Matrix.mul_apply, of_apply, ← sum_coeff_Q_mul_hE a i.2, ← sum_range_reflect,
    ← Fin.sum_univ_eq_sum_range (fun r => (Qpoly a n i).coeff (n - 1 - r)
      * hE a n ((((l + stair n) j : ℕ) : ℤ) - ((n - 1 - r : ℕ) : ℤ)))]
  refine Fintype.sum_congr _ _ fun k => ?_
  have hk := k.2
  have hj := j.2
  simp only [of_apply, Pi.add_apply, stair, cMat, transpose_apply, jtMat]
  congr 2
  omega

/-- The Jacobi–Trudi determinant of the empty shape is `1` (unitriangular). -/
theorem det_jtMat_zero_shape {N : ℕ} (a : ℕ → R) (m : ℕ) : det (jtMat a m (0 : Fin N → ℕ)) = 1 := by
  rw [det_of_isUpperTriangular]
  · exact prod_eq_one fun i _ => by simp [jtMat, hE_zero_index]
  · intro i j hij
    simp only [jtMat, of_apply, Pi.zero_apply, CharP.cast_eq_zero, zero_sub]
    exact hE_neg a m (by have : (j : ℕ) < i := hij; omega)

/-- **The bialternant formula**, Jacobi–Trudi form, over any commutative ring and for every
`l : Fin n → ℕ`: `a_{l+δ} = a_δ · det (h_{l_i − i + j}(a₀, …, a_{n−1}))`. -/
theorem altV_add_stair (a : ℕ → R) (n : ℕ) (l : Fin n → ℕ) :
    altV a n (l + stair n) = altV a n (stair n) * det (jtMat a n l) := by
  have h0 := alt_eq_mul a n 0
  rw [zero_add] at h0
  rw [altV, altV, alt_eq_mul, h0, det_mul, det_mul, det_transpose, det_transpose,
    det_jtMat_zero_shape, mul_one]

/-- **The bialternant formula**: for antitone `l`, `a_{l+δ} = a_δ · s_l(a₀, …, a_{n−1})`, with
`s_l` the tableau Schur polynomial. -/
theorem altV_add_stair_eq_mul_schurV (a : ℕ → R) (n : ℕ) (l : Fin n → ℕ) (hl : Antitone l) :
    altV a n (l + stair n) = altV a n (stair n) * schurV a n n l := by
  rw [altV_add_stair, schurV_eq_det a n l hl]

end Bialternant

/-! ## The dual Pieri rule -/

section Pieri

variable {R : Type*} [CommRing R]

/-- The elementary symmetric polynomial `e_k(a₀, …, a_{n−1}) = Σ_{|S| = k} ∏_{i ∈ S} a_i`. -/
noncomputable def eV (a : ℕ → R) (n k : ℕ) : R :=
  ∑ S ∈ (univ : Finset (Fin n)).powersetCard k, ∏ i ∈ S, a i

/-- The indicator vector `1_J`. -/
def ind {n : ℕ} (J : Finset (Fin n)) : Fin n → ℕ := fun i => if i ∈ J then 1 else 0

/-- **`e_k` raises one exponent in each of `k` columns**:
`e_k · a_μ = Σ_{|J| = k} a_{μ + 1_J}`. -/
theorem esymm_mul_altV (a : ℕ → R) (n k : ℕ) (μ : Fin n → ℕ) :
    eV a n k * altV a n μ = ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, altV a n (μ + ind J) := by
  simp only [altV, det_apply, mul_sum, eV, sum_mul]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  refine sum_nbij' (fun S : Finset (Fin n) => S.map σ.symm.toEmbedding)
    (fun J : Finset (Fin n) => J.map σ.toEmbedding) ?_ ?_ ?_ ?_ ?_
  · intro S hS; simpa using hS
  · intro J hJ; simpa using hJ
  · intro S _; ext; simp
  · intro J _; ext; simp
  · intro S _
    have key : ∏ i, a (σ i : ℕ) ^ (if i ∈ S.map σ.symm.toEmbedding then 1 else 0)
        = ∏ i ∈ S, a i := by
      simp only [mem_map_equiv, Equiv.symm_symm]
      rw [Equiv.prod_comp σ (fun x => a x ^ (if x ∈ S then 1 else 0))]
      simp [pow_ite, prod_ite_mem]
    simp only [of_apply, Pi.add_apply, ind, pow_add, prod_mul_distrib, key, Units.smul_def,
      zsmul_eq_mul]
    ring

/-- An alternant with two equal exponents vanishes. -/
theorem altV_eq_zero {a : ℕ → R} {n : ℕ} {μ : Fin n → ℕ} {j j' : Fin n} (hjj : j ≠ j')
    (h : μ j = μ j') : altV a n μ = 0 :=
  det_zero_of_column_eq hjj fun i => by simp [h]

/-- If `l` is antitone and `l + 1_J` is not, two exponents of `l + 1_J + δ` coincide. -/
theorem altV_add_ind_eq_zero (a : ℕ → R) {n : ℕ} {l : Fin n → ℕ} (hl : Antitone l)
    {J : Finset (Fin n)} (hJ : ¬ Antitone (l + ind J)) :
    altV a n (l + ind J + stair n) = 0 := by
  cases n with
  | zero => exact absurd (fun i => i.elim0) hJ
  | succ n =>
    rw [Fin.antitone_iff_succ_le] at hJ
    push Not at hJ
    obtain ⟨i, hi⟩ := hJ
    have h1 := hl (Fin.castSucc_le_succ i)
    refine altV_eq_zero (j := i.castSucc) (j' := i.succ) (Fin.castSucc_lt_succ (i := i)).ne ?_
    simp only [Pi.add_apply, ind, stair, Fin.val_castSucc, Fin.val_succ] at hi ⊢
    have := i.2
    split_ifs at hi ⊢ <;> omega

/-- Values `g₀, …, g_{n−1}` extended by `0` to `ℕ`. -/
def extFin {M : Type*} [Zero M] {n : ℕ} (g : Fin n → M) : ℕ → M :=
  fun i => if h : i < n then g ⟨i, h⟩ else 0

/-- `extFin g` restricts to `g`. -/
@[simp] theorem extFin_val {M : Type*} [Zero M] {n : ℕ} (g : Fin n → M) (i : Fin n) :
    extFin g i = g i := by
  simp [extFin]

/-- The generic point `x₀, …, x_{n−1}` of `R[x₀, …, x_{n−1}]`, extended by `0`. -/
noncomputable def genPt (R : Type*) [CommRing R] (n : ℕ) : ℕ → MvPolynomial (Fin n) R :=
  extFin MvPolynomial.X

/-- Evaluating the generic point at `g` gives `g` (below `n`). -/
theorem eval₂_genPt {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (g : Fin n → S) : ∀ i < n, (MvPolynomial.eval₂Hom f g ∘ genPt R n) i = extFin g i :=
  fun i hi => by simp [genPt, extFin, hi]

/-- At the generic point the Vandermonde alternant `a_δ` is nonzero. -/
theorem altV_genPt_stair_ne_zero (n : ℕ) : altV (genPt ℤ n) n (stair n) ≠ 0 := by
  have : (of fun i j : Fin n => genPt ℤ n i ^ stair n j)
      = (vandermonde fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ)).submatrix id
          Fin.revPerm := by
    refine Matrix.ext fun i j => ?_
    simp [genPt, extFin, stair, vandermonde, Fin.val_rev]
    congr 1
    omega
  rw [altV, this, det_permute']
  refine mul_ne_zero (by simp) ?_
  rw [det_vandermonde_ne_zero_iff]
  exact MvPolynomial.X_injective

/-- `k`-subsets as a filter. -/
theorem powersetCard_univ_eq_filter {n : ℕ} (k : ℕ) :
    (univ : Finset (Fin n)).powersetCard k = univ.filter fun J => J.card = k := by
  ext J
  simp

/-- Ring homomorphisms commute with `e_k`. -/
theorem map_eV {S : Type*} [CommRing S] (f : R →+* S) (a : ℕ → R) (n k : ℕ) :
    f (eV a n k) = eV (f ∘ a) n k := by
  simp [eV, map_sum, map_prod]

/-- `e_k(a₀, …, a_{n−1})` depends only on `a₀, …, a_{n−1}`. -/
theorem eV_congr {a b : ℕ → R} {n : ℕ} (h : ∀ i < n, a i = b i) (k : ℕ) : eV a n k = eV b n k :=
  sum_congr rfl fun _ _ => prod_congr rfl fun i _ => h i i.2

/-- The dual Pieri rule at the generic point, where `a_δ` can be cancelled. -/
theorem esymm_mul_schurV_genPt (n : ℕ) (l : Fin n → ℕ) (hl : Antitone l) (k : ℕ) :
    eV (genPt ℤ n) n k * schurV (genPt ℤ n) n n l
      = ∑ J ∈ (univ : Finset (Finset (Fin n))).filter
          (fun J => J.card = k ∧ Antitone (l + ind J)), schurV (genPt ℤ n) n n (l + ind J) := by
  refine mul_left_cancel₀ (altV_genPt_stair_ne_zero n) ?_
  rw [mul_left_comm, ← altV_add_stair_eq_mul_schurV _ n l hl, esymm_mul_altV, mul_sum,
    powersetCard_univ_eq_filter, ← sum_filter_add_sum_filter_not _ (fun J => Antitone (l + ind J)),
    filter_filter, sum_eq_zero (s := filter (fun J => ¬ Antitone (l + ind J)) _)
      fun J hJ => by rw [add_right_comm]; exact altV_add_ind_eq_zero _ hl (mem_filter.mp hJ).2,
    add_zero]
  refine sum_congr rfl fun J hJ => ?_
  rw [add_right_comm, altV_add_stair_eq_mul_schurV _ n _ (mem_filter.mp hJ).2.2]

/-- **The dual Pieri rule** over any commutative ring: for antitone `l : Fin n → ℕ`,

  `e_k(a₀, …, a_{n−1}) · s_l(a₀, …, a_{n−1}) = Σ_J s_{l + 1_J}(a₀, …, a_{n−1})`,

the sum over the `k`-subsets `J ⊆ [n]` with `l + 1_J` antitone: `l + 1_J` runs over the shapes
obtained from `l` by adding a vertical strip of `k` boxes. `s` is the tableau Schur polynomial
`schurV`; the statement mirrors the RH formalisation's `GlobalTheory.JSW.esymm_mul_schur`. -/
theorem esymm_mul_schurV (a : ℕ → R) (n : ℕ) (l : Fin n → ℕ) (hl : Antitone l) (k : ℕ) :
    eV a n k * schurV a n n l
      = ∑ J ∈ (univ : Finset (Finset (Fin n))).filter
          (fun J => J.card = k ∧ Antitone (l + fun i => if i ∈ J then 1 else 0)),
        schurV a n n (l + fun i => if i ∈ J then 1 else 0) := by
  let f : MvPolynomial (Fin n) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) fun i => a i
  have hf : ∀ i < n, (f ∘ genPt ℤ n) i = a i := fun i hi => by simp [f, genPt, extFin, hi]
  have h := congrArg f (esymm_mul_schurV_genPt n l hl k)
  rw [map_mul, map_eV, map_schurV, map_sum, eV_congr hf, schurV_congr hf] at h
  rw [h]
  exact sum_congr rfl fun J _ => by rw [map_schurV, schurV_congr hf]; rfl

end Pieri

end RMT.Symmetric
