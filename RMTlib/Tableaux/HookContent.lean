import RMTlib.Tableaux.HookLengthFormula
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import MeaningLib.Frame.Pattern

/-!
# The hook-content formula

`#SSYT(ν, n) · H(ν) = ∏_{(i,c) ∈ ν} (n + c − i)`, where `#SSYT(ν, n) = s_ν(1^n)` counts
semistandard tableaux of shape `ν` with entries `≤ n` and `H(ν)` is the hook product.

The tableaux are counted as Gelfand–Tsetlin patterns (`gtCount`): branching
`U(n) ⊃ U(n−1)` sums over `μ` interlacing `ν`. This is the index set of the RH formalisation's
basis of the dual Weyl module (`RMT.Weyl.interlaced_iff_gt`).

Proof:
- `B(x) = det [C(x_i, j)]` is multilinear in its rows. So summing `B(ℓ(μ))` over the interlacing
  box, with entries `ℓ(ν)_{i+1} ≤ ℓ(μ)_i < ℓ(ν)_i`, sums each row separately (`sum_box_binDet`).
- The hockey-stick identity turns each entry into `C(ℓ_i, j+1) − C(ℓ_{i+1}, j+1)`.
- A row operation and an expansion along the column of ones give `(−1)^n B_{n+1}(ℓ(ν))`
  (`binDet_succ`, `sum_branch_binDet`).
- Induction on `n` gives Weyl's dimension formula `#GT(ν) = B(ℓ(ν))/B(ℓ(0))`
  (`gtCount_eq_binDet`). The signs cancel, so no constant is ever computed.
- `B` is a fixed multiple of the Vandermonde product (Mathlib's `descPochhammer` form of the
  Vandermonde determinant). Frobenius's identity then gives `hook_content_formula`.

As `n → ∞`, `#SSYT(ν, n)/n^{|ν|} → 1/H(ν) = f^ν/|ν|!`: the contents drop out. For the
`k × k` square this is the integer-point value `ksConst k` of the Keating–Snaith limit.
-/

open Finset Matrix
open scoped Nat

namespace RMT

/-! ### The binomial determinant `B(x) = det [C(x_i, j)]` -/

/-- `B(x) = det [C(x_i, j)]_{i,j<n}`, a multiple of the Vandermonde determinant of `x`. -/
def binDet {n : ℕ} (x : Fin n → ℕ) : ℚ := det (of fun i j : Fin n => ((x i).choose j : ℚ))

/-- Hockey stick: `Σ_{p ≤ x < q} C(x, j) = C(q, j+1) − C(p, j+1)`. -/
theorem sum_Ico_choose (p q j : ℕ) (h : p ≤ q) :
    ∑ x ∈ Ico p q, (x.choose j : ℚ) = (q.choose (j + 1) : ℚ) - (p.choose (j + 1) : ℚ) := by
  have hr : ∀ q, ∑ x ∈ range q, (x.choose j : ℚ) = (q.choose (j + 1) : ℚ) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [sum_range_succ, ih, Nat.choose_succ_succ' q j]; push_cast; ring
  rw [sum_Ico_eq_sub _ h, hr, hr]

/-- Summing `B` over a box of rows: multilinearity of the determinant in its rows. -/
theorem sum_box_binDet {n : ℕ} (p q : Fin n → ℕ) (h : ∀ i, p i ≤ q i) :
    ∑ m ∈ Fintype.piFinset (fun i => Ico (p i) (q i)), binDet m =
      det (of fun i j : Fin n =>
        (((q i).choose (j + 1) : ℕ) : ℚ) - (((p i).choose (j + 1) : ℕ) : ℚ)) := by
  have := (detRowAlternating : (Fin n → ℚ) [⋀^Fin n]→ₗ[ℚ] ℚ).toMultilinearMap.map_sum_finset
    (fun (_ : Fin n) (x : ℕ) => fun j : Fin n => ((x.choose j : ℕ) : ℚ)) (fun i => Ico (p i) (q i))
  simp only [AlternatingMap.coe_multilinearMap] at this
  unfold binDet
  rw [show (of fun i j : Fin n =>
        (((q i).choose (j + 1) : ℕ) : ℚ) - (((p i).choose (j + 1) : ℕ) : ℚ)) =
      fun i => ∑ x ∈ Ico (p i) (q i), fun j : Fin n => ((x.choose j : ℕ) : ℚ) by
    funext i j
    rw [Finset.sum_apply, sum_Ico_choose _ _ _ (h i)]
    rfl]
  exact this.symm

/-- Subtracting each row from the one above, then expanding along the column of ones:
`B_{n+1}(a) = (−1)^n det [C(a_i, j+1) − C(a_{i+1}, j+1)]_{i,j<n}`. -/
theorem binDet_succ {n : ℕ} (a : Fin (n + 1) → ℕ) :
    binDet a = (-1) ^ n * det (of fun i j : Fin n =>
      (((a i.castSucc).choose (j + 1) : ℕ) : ℚ) - (((a i.succ).choose (j + 1) : ℕ) : ℚ)) := by
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := of fun i j => ((a i).choose j : ℚ) with hM
  set L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
    of fun i k => if k = i then 1 else if (k : ℕ) = i + 1 then -1 else 0 with hLdef
  have hL : det L = 1 := by
    rw [det_of_isUpperTriangular]
    · simp [hLdef]
    · intro i j hij
      have : (j : ℕ) < i := hij
      simp only [hLdef, of_apply]
      rw [ite_eq_right (by rintro rfl; exact lt_irrefl _ hij), ite_eq_right (by omega)]
  have hLM : ∀ i j, (L * M) i j =
      if h : (i : ℕ) < n then M i j - M ⟨i + 1, by omega⟩ j else M i j := by
    intro i j
    rw [Matrix.mul_apply]
    split_ifs with h
    · rw [Fintype.sum_eq_add i ⟨i + 1, by omega⟩ (by simp [Fin.ext_iff]) (fun k hk => by
        simp only [hLdef, of_apply]
        rw [ite_eq_right hk.1, ite_eq_right (by intro e; exact hk.2 (Fin.ext e))]
        ring)]
      have hne : (⟨i + 1, by omega⟩ : Fin (n + 1)) ≠ i := by simp [Fin.ext_iff]
      simp only [hLdef, of_apply, ite_eq_right hne]
      simp
      ring
    · rw [Fintype.sum_eq_single i (fun k hk => by
        simp only [hLdef, of_apply]
        rw [ite_eq_right hk, ite_eq_right (by have := k.isLt; omega)]
        ring)]
      simp [hLdef]
  have hdet : binDet a = det (L * M) := by rw [det_mul, hL, one_mul]; rfl
  rw [hdet, det_succ_column _ 0, Fintype.sum_eq_single (Fin.last n) (fun i hi => by
    have h : (i : ℕ) < n := by
      have := i.isLt
      have : (i : ℕ) ≠ n := fun e => hi (Fin.ext e)
      omega
    rw [hLM, dite_eq_left h]
    simp [hM])]
  rw [hLM, dite_eq_right (by simp)]
  simp only [hM, of_apply, Fin.val_last, Fin.val_zero, add_zero, Nat.choose_zero_right,
    Nat.cast_one, mul_one, Fin.succAbove_last, Fin.succAbove_zero]
  congr 2
  ext i j
  simp only [submatrix_apply, of_apply]
  rw [hLM, dite_eq_left (by simp)]
  simp only [hM, of_apply, Fin.val_succ, Fin.val_castSucc]
  congr

/-! ### Gelfand–Tsetlin patterns -/

/-- The number of Gelfand–Tsetlin patterns with top row `ν` (`n` rows): by branching
`U(n) ⊃ U(n−1)`, the sum over `μ` interlacing `ν` (`ν_{i+1} ≤ μ_i ≤ ν_i`). Equivalently, the
number of semistandard Young tableaux of shape `ν` with entries `≤ n`, i.e. `s_ν(1^n)`, the
dimension of the irreducible `U(n)`-module of highest weight `ν`. -/
def gtCount : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 1
  | n + 1, ν => ∑ μ ∈ Fintype.piFinset (fun i : Fin n => Icc (ν i.succ) (ν i.castSucc)), gtCount n μ

/-- The branching box in shifted coordinates `m = ℓ(μ)`. -/
theorem map_ell_box {n : ℕ} (ν : Fin (n + 1) → ℕ) :
    (Fintype.piFinset (fun i : Fin n => Icc (ν i.succ) (ν i.castSucc))).map
        ⟨fun μ => ell μ, fun μ μ' h => funext fun i => by
          have := congrFun h i; change ell μ i = ell μ' i at this; simp only [ell] at this
          omega⟩ =
      Fintype.piFinset (fun i : Fin n => Ico (ell ν i.succ) (ell ν i.castSucc)) := by
  ext m
  simp only [mem_map, Fintype.mem_piFinset, mem_Icc, mem_Ico]
  constructor
  · rintro ⟨μ, hμ, rfl⟩ i
    have h1 := hμ i
    have hi := i.isLt
    show ell ν i.succ ≤ ell μ i ∧ ell μ i < ell ν i.castSucc
    simp only [ell, Fin.val_succ, Fin.val_castSucc]
    omega
  · intro hm
    refine ⟨fun i => m i - (n - 1 - i), fun i => ?_, funext fun i => ?_⟩
    · have h1 := hm i
      have hi := i.isLt
      simp only [ell, Fin.val_succ, Fin.val_castSucc] at h1 ⊢
      omega
    · have h1 := hm i
      have hi := i.isLt
      show ell (fun i : Fin n => m i - (n - 1 - i)) i = m i
      simp only [ell, Fin.val_succ, Fin.val_castSucc] at h1 ⊢
      omega

/-- **Branching sum of `B`**: summing `B(ℓ(μ))` over `μ` interlacing `ν` gives `(−1)^n B(ℓ(ν))`. -/
theorem sum_branch_binDet {n : ℕ} (ν : Fin (n + 1) → ℕ) (hν : Antitone ν) :
    ∑ μ ∈ Fintype.piFinset (fun i : Fin n => Icc (ν i.succ) (ν i.castSucc)), binDet (ell μ) =
      (-1) ^ n * binDet (ell ν) := by
  rw [show ∑ μ ∈ Fintype.piFinset (fun i : Fin n => Icc (ν i.succ) (ν i.castSucc)),
      binDet (ell μ) = ∑ m ∈ Fintype.piFinset (fun i : Fin n => Ico (ell ν i.succ) (ell ν i.castSucc)),
      binDet m by rw [← map_ell_box, sum_map]; rfl,
    sum_box_binDet _ _ (fun i => by
      have := (ell_strictAnti hν) (Fin.castSucc_lt_succ (i := i)); omega), binDet_succ,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem antitone_of_mem_box {n : ℕ} {ν : Fin (n + 1) → ℕ} (hν : Antitone ν) {μ : Fin n → ℕ}
    (hμ : μ ∈ Fintype.piFinset (fun i : Fin n => Icc (ν i.succ) (ν i.castSucc))) : Antitone μ := by
  rw [Fintype.mem_piFinset] at hμ
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have h1 := (mem_Icc.mp (hμ j)).2
    have h2 := (mem_Icc.mp (hμ i)).1
    have h3 := hν (show i.succ ≤ j.castSucc from Fin.le_def.mpr (by
      simp only [Fin.val_succ, Fin.val_castSucc]; exact hlt))
    omega

/-- **Weyl's dimension formula, binomial form**: `#GT(ν) = B(ℓ(ν)) / B(ℓ(0))`. -/
theorem gtCount_eq_binDet (n : ℕ) :
    ∀ ν : Fin n → ℕ, Antitone ν → (gtCount n ν : ℚ) = binDet (ell ν) / binDet (ell (0 : Fin n → ℕ)) := by
  induction n with
  | zero => intro ν _; simp [gtCount, binDet]
  | succ n ih =>
    intro ν hν
    have h0 := sum_branch_binDet (0 : Fin (n + 1) → ℕ) (fun _ _ _ => le_rfl)
    have hbox0 : Fintype.piFinset (fun i : Fin n =>
        Icc ((0 : Fin (n + 1) → ℕ) i.succ) ((0 : Fin (n + 1) → ℕ) i.castSucc)) = {0} := by
      ext μ
      simp only [Fintype.mem_piFinset, Pi.zero_apply, Icc_self, mem_singleton]
      exact ⟨fun h => funext h, fun h i => congrFun h i⟩
    rw [hbox0, sum_singleton] at h0
    rw [gtCount, Nat.cast_sum, sum_congr rfl fun μ hμ => ih μ (antitone_of_mem_box hν hμ),
      ← sum_div, sum_branch_binDet ν hν, h0, mul_div_mul_left _ _ (by simp)]

/-! ### From `B` to the Vandermonde product, and to hook-contents -/

/-- `B(x) = c_n · ∏_{i<j}(x_i − x_j)` with `c_n ≠ 0` independent of `x`. -/
theorem binDet_eq_mul_vand {n : ℕ} :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ x : Fin n → ℕ, binDet x = c * vand (fun i => (x i : ℚ)) := by
  set s : ℚ := ∏ i : Fin n, ∏ _j ∈ Ioi i, (-1 : ℚ)
  set P : ℚ := ∏ j : Fin n, ((j : ℕ)! : ℚ) with hPdef
  have hs : s ≠ 0 := prod_ne_zero_iff.mpr fun _ _ => prod_ne_zero_iff.mpr fun _ _ => by norm_num
  have hP : P ≠ 0 := prod_ne_zero_iff.mpr fun _ _ => by positivity
  refine ⟨s / P, div_ne_zero hs hP, fun x => ?_⟩
  have hV := det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i => (x i : ℚ))
    (fun i => descPochhammer ℚ i) (fun i => descPochhammer_natDegree ℚ i)
    (fun i => monic_descPochhammer ℚ i)
  have hD : (of fun i j : Fin n => (descPochhammer ℚ j).eval ((x i : ℕ) : ℚ)) =
      of fun i j : Fin n => ((j : ℕ)! : ℚ) * ((x i).choose j : ℚ) := by
    ext i j
    simp only [of_apply, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  have hm := det_mul_row (fun j : Fin n => ((j : ℕ)! : ℚ)) (of fun i j : Fin n => ((x i).choose j : ℚ))
  simp only [of_apply] at hm
  rw [hD, hm, det_vandermonde] at hV
  have hsv : ∏ i : Fin n, ∏ j ∈ Ioi i, ((x j : ℚ) - x i) = s * vand (fun i => (x i : ℚ)) := by
    rw [vand, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun j _ => by ring
  rw [hsv] at hV
  unfold binDet
  rw [div_mul_eq_mul_div, eq_div_iff hP, hV, hPdef]
  ring

theorem hookProd_mul_vand {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    (hookProd ν : ℚ) * vand (ellQ ν) = ∏ i, ((ell ν i)! : ℚ) := by
  rw [vand_ellQ hν]
  exact_mod_cast frobenius ν hν

theorem factorial_add_eq_mul_prod (a k : ℕ) : (a + k)! = a ! * ∏ c ∈ range k, (a + 1 + c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, ih, prod_range_succ]
    ring

/-- **The hook-content formula**: the number of semistandard Young tableaux of shape `ν` with
entries `≤ n` (Gelfand–Tsetlin patterns with top row `ν`) satisfies
`#SSYT(ν, n) · H(ν) = ∏_{(i,c) ∈ ν} (n + c − i)`. -/
@[frame_pattern]
theorem hook_content_formula (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) :
    gtCount n ν * hookProd ν = ∏ i : Fin n, ∏ c ∈ range (ν i), (n - i + c) := by
  obtain ⟨cn, hc, hB⟩ := binDet_eq_mul_vand (n := n)
  have h0 : Antitone (0 : Fin n → ℕ) := fun _ _ _ => le_rfl
  have hH0 : hookProd (0 : Fin n → ℕ) = 1 := by simp [hookProd]
  have hV0 := hookProd_mul_vand 0 h0
  rw [hH0, Nat.cast_one, one_mul] at hV0
  have hV := hookProd_mul_vand ν hν
  have hF0 : (∏ i, ((ell (0 : Fin n → ℕ) i)! : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun _ _ => by positivity
  have hq : (gtCount n ν : ℚ) * hookProd ν =
      (∏ i, ((ell ν i)! : ℚ)) / ∏ i, ((ell (0 : Fin n → ℕ) i)! : ℚ) := by
    rw [gtCount_eq_binDet n ν hν, hB, hB, mul_div_mul_left _ _ hc]
    change vand (ellQ ν) / vand (ellQ 0) * _ = _
    rw [← hV, ← hV0]
    field_simp
  have hprod : (∏ i, ((ell ν i)! : ℚ)) =
      (∏ i, ((ell (0 : Fin n → ℕ) i)! : ℚ)) * ∏ i : Fin n, ∏ c ∈ range (ν i), ((n - i + c : ℕ) : ℚ) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    have hi := i.isLt
    rw [show ell ν i = (n - 1 - i) + ν i by simp only [ell]; ring, factorial_add_eq_mul_prod]
    simp only [ell, Pi.zero_apply, zero_add]
    push_cast
    congr 1
    refine prod_congr rfl fun c _ => ?_
    rw [show n - (i : ℕ) = (n - 1 - i) + 1 by omega]
    push_cast
    ring
  rw [hprod, mul_div_cancel_left₀ _ hF0] at hq
  exact_mod_cast hq

end RMT
