import RMTlib.Places.CyclotomicBertrand

/-!
# The central `q`-binomial `Q`: the Bertrand video's remaining captions

`Q n = ∏_{1 < d ≤ 2n} Φ_d^{e_d(n)}` is the central `q`-binomial (`qFact_two_mul_Q`:
`[2n]_q! = ([n]_q!)² · Q`). This file proves the claims of DisseminationLib's Bertrand video that
`RMTlib.Places.CyclotomicBertrand` left as *known* or *computed*:

* `carry_eq_one_iff_window`: **the windows**. `e_d(n) = 1` iff `n < (k+1) d` and `(2k+1) d ≤ 2n`
  for some `k` (then `k = ⌊n/d⌋`), i.e. `d ∈ (n/(k+1), n/(k+½)]`.
* `natDegree_Q`: **`Q` has degree `n²`** (degrees of `q`-factorials, `natDegree_qInt`,
  `two_mul_natDegree_qFact`, from `deg Φ_d = φ(d)` and `Σ_{d ∣ j} φ(d) = j`).
* `root_of_unity_of_isRoot`: **every complex root of `Q` is a root of unity**, of an order `d` with
  `e_d(n) = 1`.
* `reverse_Q`, `coeff_Q_symm`: **`Q` is a palindrome**, `[q^k] Q = [q^{n²−k}] Q`.
* `eval_neg_one_Q_eq_zero_iff`: **`Q(−1) = 0` iff `n` is odd** (`−1` is a root of `Φ_2` only, and
  `e_2(n) = n mod 2`). The value `C(n, n/2)` for even `n` (Stembridge's `q = −1` phenomenon) is not
  proved here.
* `prod_content_one_row`: **the one-row partition**: `∏_{c<n} (N + c) = n! · C(2n, n)` at `N = n+1`.

Not proved here: `Q = Σ_{λ ⊂ n×n} q^{|λ|}` (the box sum).
-/

open Finset Polynomial

namespace RMT.Places.Bertrand

/-- The central `q`-binomial `Q = [2n choose n]_q = ∏_{1 < d ≤ 2n} Φ_d^{e_d(n)}`. -/
noncomputable def Q (n : ℕ) : ℤ[X] := ∏ d ∈ Ioc 1 (2 * n), cyclotomic d ℤ ^ carry n d

theorem qFact_two_mul_Q (n : ℕ) : qFact (2 * n) = qFact n ^ 2 * Q n := qFact_two_mul n

/-! ## Windows -/

/-- **The windows**: `e_d(n) = 1` iff `n/(k+1) < d ≤ n/(k + ½)` for some `k`, i.e.
`n < (k+1) d` and `(2k+1) d ≤ 2n` (then `k = ⌊n/d⌋`). -/
theorem carry_eq_one_iff_window (n : ℕ) {d : ℕ} (hd : 0 < d) :
    carry n d = 1 ↔ ∃ k, n < (k + 1) * d ∧ (2 * k + 1) * d ≤ 2 * n := by
  rw [carry_eq n hd]
  have e := Nat.div_add_mod n d
  have hr := Nat.mod_lt n hd
  constructor
  · intro h
    split_ifs at h with hw
    · refine ⟨n / d, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨k, h1, h2⟩
    have hk : k = n / d := by
      apply le_antisymm
      · rw [Nat.le_div_iff_mul_le hd]; nlinarith
      · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hd]; linarith
    subst hk
    rw [ite_eq_left (by nlinarith)]

/-! ## The one-row partition at `N = n + 1` -/

/-- **`C(2n, n)` is the hook-content number of the one-row partition `(n)` at `N = n + 1`**:
`∏_{c < n} (N + c) = n! · C(2n, n)`. -/
theorem prod_content_one_row (n : ℕ) :
    ∏ c ∈ range n, (n + 1 + c) = n.factorial * (2 * n).choose n := by
  rw [show 2 * n = n + n by ring, ← Nat.ascFactorial_eq_factorial_mul_choose,
    Nat.ascFactorial_eq_prod_range]

/-! ## `Q(−1)` -/

theorem carry_two (n : ℕ) : carry n 2 = n % 2 := by
  rw [carry_eq n (by norm_num)]; split_ifs <;> omega

/-- `−1` is a root of `Φ_d` (`d ≥ 1`) only for `d = 2`. -/
theorem eval_neg_one_cyclotomic_eq_zero_iff {d : ℕ} (hd : 0 < d) :
    (cyclotomic d ℤ).eval (-1) = 0 ↔ d = 2 := by
  have : NeZero (d : ℤ) := ⟨by exact_mod_cast hd.ne'⟩
  rw [← IsRoot.def, isRoot_cyclotomic_iff]
  have h2 : IsPrimitiveRoot (-1 : ℤ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  exact ⟨fun h => h.unique h2, fun h => h ▸ h2⟩

/-- **`Q(−1) = 0` exactly for odd `n`**: `−1` is a zero of `Φ_2` only, and `e_2(n) = n mod 2`. -/
theorem eval_neg_one_Q_eq_zero_iff (n : ℕ) : (Q n).eval (-1) = 0 ↔ Odd n := by
  rw [Q, eval_prod, prod_eq_zero_iff]
  simp_rw [eval_pow]
  constructor
  · rintro ⟨d, hd, h⟩
    have hd' := mem_Ioc.mp hd
    rcases Nat.eq_zero_or_pos (carry n d) with h0 | hpos
    · rw [h0, pow_zero] at h; exact absurd h one_ne_zero
    · rw [pow_eq_zero_iff hpos.ne', eval_neg_one_cyclotomic_eq_zero_iff (by omega)] at h
      subst h; rw [carry_two] at hpos; exact Nat.odd_iff.mpr (by omega)
  · intro ho
    have h1 := Nat.odd_iff.mp ho
    refine ⟨2, mem_Ioc.mpr ⟨by norm_num, by omega⟩, ?_⟩
    rw [carry_two, h1, pow_one, eval_neg_one_cyclotomic_eq_zero_iff (by norm_num)]

/-! ## Degree `n²` -/

theorem natDegree_qInt {j : ℕ} (hj : 0 < j) : (qInt j).natDegree = j - 1 := by
  rw [qInt_eq_prod hj, natDegree_prod _ _ (fun d _ => cyclotomic_ne_zero d ℤ)]
  simp_rw [natDegree_cyclotomic]
  have := Nat.sum_totient j
  rw [← add_sum_erase _ _ (Nat.one_mem_divisors.mpr hj.ne'), Nat.totient_one] at this
  omega

theorem qInt_ne_zero {j : ℕ} (hj : 0 < j) : qInt j ≠ 0 := by
  rw [qInt_eq_prod hj]; exact prod_ne_zero_iff.mpr fun d _ => cyclotomic_ne_zero d ℤ

theorem qFact_ne_zero (m : ℕ) : qFact m ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ hj => qInt_ne_zero (mem_Ioc.mp hj).1

theorem two_mul_natDegree_qFact (m : ℕ) : 2 * (qFact m).natDegree = m * (m - 1) := by
  induction m with
  | zero => simp [qFact]
  | succ m ih =>
    have hs : Ioc 0 (m + 1) = insert (m + 1) (Ioc 0 m) := by ext x; simp; omega
    have hne : ∏ x ∈ Ioc 0 m, qInt x ≠ 0 := qFact_ne_zero m
    rw [qFact, hs, prod_insert (by simp), natDegree_mul (qInt_ne_zero (by omega)) hne,
      natDegree_qInt (by omega)]
    rw [qFact] at ih
    rcases m with _ | m
    · simp
    · simp only [Nat.add_sub_cancel] at ih ⊢
      nlinarith

/-- **`Q` has degree `n²`.** -/
theorem natDegree_Q (n : ℕ) : (Q n).natDegree = n ^ 2 := by
  have hQ : Q n ≠ 0 := prod_ne_zero_iff.mpr fun d _ => pow_ne_zero _ (cyclotomic_ne_zero d ℤ)
  have h := congrArg natDegree (qFact_two_mul_Q n)
  rw [natDegree_mul (pow_ne_zero 2 (qFact_ne_zero n)) hQ, natDegree_pow] at h
  have hA := two_mul_natDegree_qFact (2 * n)
  have hB := two_mul_natDegree_qFact n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Q]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, Nat.add_sub_cancel] at *
    nlinarith

/-! ## Roots of unity -/

/-- **Every complex root of `Q` is a root of unity**, of an order `d` with `e_d(n) = 1`. -/
theorem root_of_unity_of_isRoot (n : ℕ) {z : ℂ} (hz : ((Q n).map (Int.castRingHom ℂ)).IsRoot z) :
    ∃ d ∈ Ioc 1 (2 * n), carry n d = 1 ∧ z ^ d = 1 := by
  rw [IsRoot.def, Q, Polynomial.map_prod, eval_prod, prod_eq_zero_iff] at hz
  obtain ⟨d, hd, h⟩ := hz
  rw [Polynomial.map_pow, eval_pow, map_cyclotomic] at h
  have hpos : carry n d ≠ 0 := fun h0 => by rw [h0, pow_zero] at h; exact one_ne_zero h
  have hc : carry n d = 1 := by have := carry_le_one n (d := d) (by have := (mem_Ioc.mp hd).1; omega); omega
  refine ⟨d, hd, hc, ?_⟩
  rw [pow_eq_zero_iff hpos] at h
  have hdvd := cyclotomic.dvd_X_pow_sub_one d ℂ
  obtain ⟨g, hg⟩ := hdvd
  have := congrArg (eval z) hg
  rw [eval_mul, h, zero_mul, eval_sub, eval_pow, eval_X, eval_one] at this
  exact sub_eq_zero.mp this

/-! ## The palindrome -/

theorem coeff_qInt (j k : ℕ) : (qInt j).coeff k = if k < j then 1 else 0 := by
  rw [qInt, finsetSum_coeff]
  simp_rw [coeff_X_pow]
  rw [sum_ite_eq]
  simp

theorem reverse_qInt {j : ℕ} (hj : 0 < j) : (qInt j).reverse = qInt j := by
  ext k
  rw [coeff_reverse, natDegree_qInt hj, coeff_qInt, coeff_qInt]
  by_cases hk : k ≤ j - 1
  · rw [revAt_le hk, ite_eq_left (show j - 1 - k < j by omega), ite_eq_left (show k < j by omega)]
  · have e : revAt (j - 1) k = k := revAt_eq_self_of_lt (by omega)
    rw [e]

theorem reverse_qFact (m : ℕ) : (qFact m).reverse = qFact m := by
  induction m with
  | zero => simp [qFact, reverse]
  | succ m ih =>
    have hs : Ioc 0 (m + 1) = insert (m + 1) (Ioc 0 m) := by ext x; simp; omega
    have e : qFact (m + 1) = qInt (m + 1) * qFact m := by rw [qFact, hs, prod_insert (by simp)]; rfl
    rw [e, reverse_mul_of_domain, reverse_qInt (by omega), ih]

/-- **`Q` is a palindrome**: `Q.reverse = Q`. -/
theorem reverse_Q (n : ℕ) : (Q n).reverse = Q n := by
  have h := congrArg reverse (qFact_two_mul_Q n)
  rw [reverse_mul_of_domain, sq, reverse_mul_of_domain, reverse_qFact, reverse_qFact] at h
  have h2 := qFact_two_mul_Q n
  rw [sq] at h2
  exact mul_left_cancel₀ (mul_ne_zero (qFact_ne_zero n) (qFact_ne_zero n)) (h.symm.trans h2)

/-- **The palindrome on coefficients**: `[q^k] Q = [q^{n² − k}] Q`. -/
theorem coeff_Q_symm (n : ℕ) {k : ℕ} (hk : k ≤ n ^ 2) :
    (Q n).coeff k = (Q n).coeff (n ^ 2 - k) := by
  conv_lhs => rw [← reverse_Q n]
  rw [coeff_reverse, natDegree_Q, revAt_le hk]

end RMT.Places.Bertrand
