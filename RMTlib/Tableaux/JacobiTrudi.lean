import RMTlib.Tableaux.HookContent
import RMTlib.Tableaux.GelfandTsetlin

/-!
# Two specialisations of the Jacobi–Trudi identity

`s_{λ/μ} = det (h_{λ_i − μ_j − i + j})`. The identity is the determinant face of the Fock /
Toeplitz-minor picture: Dehaye, *On an identity due to (Bump and Diaconis) and (Tracy and
Widom)*, Canad. Math. Bull. 54 (2011), arXiv:math/0601348, shows that the
Bump–Diaconis–Tracy–Widom formula for Toeplitz minors `det (d_{λ_i − μ_j − i + j})` is
Jacobi–Trudi differentiated by the Fock contraction `exp (Σ_k k ∂_{p_k} ∂_{p̃_k})`.

Two specialisations are proved here, with `h_k(1^n) = C(n − 1 + k, n − 1)` (`hOne`):

* `jacobiTrudi_one_variable`: in one variable the skew determinant is the interlacing indicator,
  `1` if `λ_{i+1} ≤ μ_i ≤ λ_i` (`RMT.Weyl.GTStep`, a horizontal strip) and `0` otherwise. The
  matrix is a `0/1` staircase (`det_staircase`). After the `ρ`-shift this is the RH
  formalisation's GGP interlacing condition (`RMT.Bridge.cayley_interlacing_iff`).
* `jacobiTrudiOne_eq_gtCount`: at `1^n`, `det (h_{ν_i − i + j}(1^n)) = #GT(ν) = s_ν(1^n)`. Each
  entry is a polynomial of degree `n − 1` in `ℓ_i = ν_i + n − 1 − i`, so the determinant is a
  constant times the Vandermonde product. The constant is fixed by `ν = 0`, where the matrix is
  unitriangular. Weyl's dimension formula (`RMT.gtCount_eq_binDet`) closes the comparison.

So the branching sums behind `gtCount` (products of one-variable skew Jacobi–Trudi indicators)
add up to the `n`-variable Jacobi–Trudi determinant at `1^n`.
-/

open Finset Matrix Polynomial
open scoped Nat

namespace RMT

/-- `h_k(1^n)`, the complete homogeneous symmetric polynomial of degree `k` in `n` variables at
`1`: `C(n − 1 + k, n − 1)` for `k ≥ 0`, and `0` for `k < 0`. -/
def hOne (n : ℕ) (k : ℤ) : ℚ := if 0 ≤ k then ((n - 1 + k.toNat).choose (n - 1) : ℚ) else 0

/-! ### Staircase determinants -/

theorem eq_self_of_strictMono_lt {n : ℕ} (r : Fin n → ℕ) (hr : StrictMono r)
    (hlt : ∀ i, r i < n) (i : Fin n) : r i = i := by
  have h1 : #(Iio i) ≤ #(range (r i)) :=
    card_le_card_of_injOn r (by intro j hj; simp only [coe_Iio, Set.mem_Iio, coe_range] at hj ⊢; exact hr hj)
      hr.injective.injOn
  have h2 : #(Ioi i) ≤ #(Ioo (r i) n) :=
    card_le_card_of_injOn r (by
      intro j hj; simp only [coe_Ioi, Set.mem_Ioi, coe_Ioo, Set.mem_Ioo] at hj ⊢
      exact ⟨hr hj, hlt j⟩) hr.injective.injOn
  simp only [Fin.card_Iio, card_range, Fin.card_Ioi, Nat.card_Ioo] at h1 h2
  have := hlt i
  omega

/-- A `0/1` staircase `[r_i ≤ j]` with `r` monotone has determinant `1` if `r = id`, else `0`. -/
theorem det_staircase {n : ℕ} (r : Fin n → ℕ) (hr : Monotone r) :
    det (of fun i j : Fin n => if r i ≤ j then (1 : ℚ) else 0) =
      if ∀ i : Fin n, r i = i then 1 else 0 := by
  split_ifs with h
  · rw [det_of_isUpperTriangular]
    · exact prod_eq_one fun i _ => by simp [h i]
    · intro i j hij
      have : (j : ℕ) < i := hij
      simp only [of_apply, h i]
      rw [if_neg (by omega)]
  · by_contra hdet
    have hinj : Function.Injective r := by
      intro i i' hii'
      by_contra hne
      exact hdet (det_zero_of_row_eq hne (funext fun j => by simp [hii']))
    have hlt : ∀ i, r i < n := by
      intro i
      by_contra hge
      push Not at hge
      exact hdet (det_eq_zero_of_row_eq_zero i fun j => by
        simp only [of_apply]; rw [if_neg (by have := j.isLt; omega)])
    exact h (eq_self_of_strictMono_lt r (hr.strictMono_of_injective hinj) hlt)

/-- A down-closed subset of `Fin n` is the initial segment of its cardinality. -/
theorem mem_iff_lt_card {n : ℕ} (S : Finset (Fin n))
    (hS : ∀ j j' : Fin n, j' ≤ j → j ∈ S → j' ∈ S) (j : Fin n) : j ∈ S ↔ (j : ℕ) < #S := by
  constructor
  · intro hj
    have := card_le_card (show Iic j ⊆ S from fun j' hj' => hS j j' (mem_Iic.mp hj') hj)
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra hj
    have := card_le_card (show S ⊆ Iio j from fun s hs => mem_Iio.mpr (by
      by_contra hge; push Not at hge; exact hj (hS s j hge hs)))
    rw [Fin.card_Iio] at this
    omega

/-! ### Skew Jacobi–Trudi in one variable: the interlacing indicator -/

theorem hOne_one (k : ℤ) : hOne 1 k = if 0 ≤ k then 1 else 0 := by
  simp [hOne]

open Classical in
/-- **Skew Jacobi–Trudi in one variable** (at `x = 1`): `det (h_{λ_i − μ_j − i + j})` is `1` when
`μ` interlaces `λ` (`λ_{i+1} ≤ μ_i ≤ λ_i`, i.e. `λ/μ` is a horizontal strip: Gelfand–Tsetlin
branching, `RMT.Weyl.GTStep`), and `0` otherwise. With `ρ`-shifted parameters this is the
GGP interlacing condition of the RH formalisation (`RMT.Bridge.cayley_interlacing_iff`). -/
theorem jacobiTrudi_one_variable {n : ℕ} (lam mu : Fin n → ℕ) (hl : Antitone lam)
    (hm : Antitone mu) :
    det (of fun i j : Fin n => hOne 1 ((lam i : ℤ) - mu j - i + j)) =
      if Weyl.GTStep lam mu then 1 else 0 := by
  set S : Fin n → Finset (Fin n) := fun i => {j | (lam i : ℤ) - i < (mu j : ℤ) - j} with hSdef
  set r : Fin n → ℕ := fun i => #(S i) with hrdef
  have hS : ∀ i j, j ∈ S i ↔ (j : ℕ) < r i := fun i => mem_iff_lt_card (S i) (fun j j' hjj' hj => by
    simp only [hSdef, mem_filter, mem_univ, true_and] at hj ⊢
    have := hm hjj'
    have : (j' : ℕ) ≤ j := hjj'
    omega)
  have hmem : ∀ i j, j ∈ S i ↔ (lam i : ℤ) - i < (mu j : ℤ) - j := fun i j => by
    simp [hSdef]
  have hentry : ∀ i j : Fin n,
      hOne 1 ((lam i : ℤ) - mu j - i + j) = if r i ≤ j then 1 else 0 := by
    intro i j
    have h1 := hS i j
    rw [hmem] at h1
    rw [hOne_one]
    by_cases h : r i ≤ (j : ℕ)
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  have hr : Monotone r := fun i i' h => card_le_card fun j hj => by
    rw [hmem] at hj ⊢
    have := hl h
    have : (i : ℕ) ≤ i' := h
    omega
  have key : (∀ i : Fin n, r i = i) ↔ Weyl.GTStep lam mu := by
    constructor
    · intro h
      refine ⟨fun l j hj => ?_, fun t => ?_⟩
      · have := (hS j l).mpr (by rw [h j]; omega)
        rw [hmem] at this
        omega
      · have : t ∉ S t := fun ht => by have := (hS t t).mp ht; rw [h t] at this; omega
        rw [hmem] at this
        omega
    · rintro ⟨hstep, hle⟩ i
      have hup : r i ≤ i := by
        by_contra hlt
        push Not at hlt
        have := (hmem i i).mp ((hS i i).mpr hlt)
        have := hle i
        omega
      rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
      · omega
      · have hl' : (⟨i - 1, by omega⟩ : Fin n) ∈ S i := by
          rw [hmem]
          have := hstep ⟨i - 1, by omega⟩ i (by simp; omega)
          simp only at this ⊢
          push_cast [Nat.cast_sub (by omega : 1 ≤ (i : ℕ))]
          omega
        have := (hS i _).mp hl'
        simp only at this
        omega
  rw [show (of fun i j : Fin n => hOne 1 ((lam i : ℤ) - mu j - i + j)) =
      of fun i j : Fin n => if r i ≤ j then (1 : ℚ) else 0 from by ext i j; simp only [of_apply, hentry],
    det_staircase r hr]
  by_cases hg : Weyl.GTStep lam mu
  · rw [if_pos (key.mpr hg), if_pos hg]
  · rw [if_neg (fun h => hg (key.mp h)), if_neg hg]

/-! ### Jacobi–Trudi at `1^n` -/

/-- The Jacobi–Trudi determinant `det (h_{ν_i − i + j}(1^n))`, i.e. `s_ν(1^n)`. -/
def jacobiTrudiOne (n : ℕ) (ν : Fin n → ℕ) : ℚ :=
  det (of fun i j : Fin n => hOne n ((ν i : ℤ) - i + j))

theorem hOne_entry {n : ℕ} (ν : Fin n → ℕ) (i j : Fin n) :
    hOne n ((ν i : ℤ) - i + j) = ((ell ν i + j).choose (n - 1) : ℚ) := by
  have hi := i.isLt
  unfold hOne
  split_ifs with h
  · congr 2
    simp only [ell]
    omega
  · rw [Nat.choose_eq_zero_of_lt (by simp only [ell]; omega)]
    simp

/-- A matrix of polynomial values with all degrees `< n` factors through the Vandermonde matrix. -/
theorem eval_matrix_eq_vandermonde_mul {n : ℕ} (v : Fin n → ℚ) (p : Fin n → ℚ[X])
    (h_deg : ∀ j, (p j).natDegree < n) :
    of (fun i j => (p j).eval (v i)) =
      vandermonde v * of (fun (i j : Fin n) => (p j).coeff i) := by
  ext i j
  simp_rw [mul_apply, eval, of_apply, eval₂_eq_sum]
  simp only [vandermonde]
  have : (p j).support ⊆ range n := supp_subset_range (h_deg j)
  rw [Polynomial.sum_eq_of_subset _ (fun j => zero_mul ((v i) ^ j)) this, ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [mul_comm, of_apply, RingHom.id_apply]

/-- The polynomial `x ↦ C(x + j, n − 1)`. -/
noncomputable def binPoly (n j : ℕ) : ℚ[X] :=
  C ((1 : ℚ) / ((n - 1)! : ℚ)) * (descPochhammer ℚ (n - 1)).comp (X + C (j : ℚ))

theorem binPoly_eval (n j x : ℕ) : (binPoly n j).eval (x : ℚ) = ((x + j).choose (n - 1) : ℚ) := by
  simp only [binPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X]
  rw [show (x : ℚ) + j = ((x + j : ℕ) : ℚ) by push_cast; ring, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

theorem binPoly_natDegree (n j : ℕ) : (binPoly n j).natDegree ≤ n - 1 := by
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_comp, descPochhammer_natDegree, natDegree_X_add_C, mul_one]

/-- The Vandermonde determinant against the triangular product. -/
theorem det_vandermonde_eq_mul_vand {n : ℕ} :
    ∃ s : ℚ, ∀ x : Fin n → ℚ, det (vandermonde x) = s * vand x := by
  refine ⟨∏ i : Fin n, ∏ _j ∈ Ioi i, (-1 : ℚ), fun x => ?_⟩
  rw [det_vandermonde, vand, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun j _ => by ring

/-- **Jacobi–Trudi at `1^n`**: `det (h_{ν_i − i + j}(1^n)) = #GT(ν) = s_ν(1^n)`. -/
theorem jacobiTrudiOne_eq_gtCount (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) :
    jacobiTrudiOne n ν = gtCount n ν := by
  obtain ⟨s, hs⟩ := det_vandermonde_eq_mul_vand (n := n)
  obtain ⟨c, hc, hB⟩ := binDet_eq_mul_vand (n := n)
  set K := det (of fun (i j : Fin n) => (binPoly n j).coeff i) with hK
  have hdeg : ∀ j : Fin n, (binPoly n j).natDegree < n := fun j => by
    have := binPoly_natDegree n j
    have := j.isLt
    omega
  have hJT : ∀ ν' : Fin n → ℕ, jacobiTrudiOne n ν' = s * K * vand (ellQ ν') := by
    intro ν'
    have hm : (of fun i j : Fin n => hOne n ((ν' i : ℤ) - i + j)) =
        of fun i j : Fin n => (binPoly n j).eval (ellQ ν' i) := by
      ext i j
      simp only [of_apply, hOne_entry, ellQ, binPoly_eval]
    rw [jacobiTrudiOne, hm, eval_matrix_eq_vandermonde_mul _ _ hdeg, det_mul, hs]
    ring
  have h0 : jacobiTrudiOne n 0 = 1 := by
    rw [jacobiTrudiOne, det_of_isUpperTriangular]
    · refine prod_eq_one fun i _ => ?_
      simp [hOne]
    · intro i j hij
      have : (j : ℕ) < i := hij
      simp only [of_apply, Pi.zero_apply, Nat.cast_zero, hOne]
      rw [if_neg (by omega)]
  rw [hJT] at h0
  rw [gtCount_eq_binDet n ν hν, hB, hB, mul_div_mul_left _ _ hc, hJT]
  change s * K * vand (ellQ ν) = vand (ellQ ν) / vand (ellQ 0)
  rw [eq_div_iff (right_ne_zero_of_mul_eq_one h0), mul_assoc, mul_comm (vand _), ← mul_assoc, h0,
    one_mul]
end RMT
