import Mathlib

/-!
# The central `q`-binomial, cyclotomically (#145)

The first instance of the `ℙ²` "places × `q`-line" (RMTlib#145, RH-Dual's Bertrand / Erdős reading):
one polynomial, `[2n choose n]_q`, whose cyclotomic exponents are the carries of `n` in base `d`,
and whose value at `q = 1` is Chebyshev's identity.

* `carry_eq`, `carry_le_one`: **the carry `e_d(n) = ⌊2n/d⌋ − 2⌊n/d⌋` is `0` or `1`, and it is `1`
  exactly past the ½ wall**, `2 (n mod d) ≥ d` (the fractional part of `n/d` is at least `½`).
* `qInt_eq_prod`: `[j]_q = ∏_{d ∣ j, d > 1} Φ_d`.
* `qFact_eq`: `[m]_q! = ∏_{1 < d ≤ m} Φ_d^{⌊m/d⌋}`.
* `qFact_two_mul`: **`[2n]_q! = ([n]_q!)² ∏_{1 < d ≤ 2n} Φ_d^{e_d(n)}`**, so the central `q`-binomial
  is `∏ Φ_d^{e_d}`, square-free in the cyclotomic polynomials (Kummer 1852; Knuth–Wilf 1989).
* `eval_one_qFact`, `choose_eq_prod_eval`: at `q = 1`, `C(2n, n) = ∏ Φ_d(1)^{e_d}`.
* `eval_one_cyclotomic_eq`, `log_eval_one_cyclotomic`: `Φ_d(1)` is `p` for `d = p^k` and `1`
  otherwise, i.e. `log Φ_d(1) = Λ(d)`.
* `factorial_eq_prod_eval`, `log_factorial_eq_sum`: the same for `m!`, with exponents `⌊m/d⌋`
  (Legendre–Chebyshev).
* `log_choose_eq_sum_carry`: **Chebyshev's identity** `log C(2n, n) = Σ_d e_d(n) Λ(d)`: the place
  `p` collects the carries at `d = p, p², …` (Kummer's `v_p`), and the sum over places is the size
  at `∞` (the product formula of row 7, `RMT.Places.deg_principal`, `RMT.Transfer.log_eq_sum`).

In the language of #127/#145: the `q`-line carries the zeros `ζ_d` of `[2n choose n]_q`, simple,
present exactly when `{n/d} ≥ ½` (a mirror wall at `½`); specialising `q → 1` sends `ζ_{p^k}` to the
place `p`.
-/

open Finset Polynomial

namespace RMT.Places.Bertrand

/-! ## The carry exponent and the ½ wall -/

/-- The carry `e_d(n) = ⌊2n/d⌋ − 2⌊n/d⌋`. -/
def carry (n d : ℕ) : ℕ := 2 * n / d - 2 * (n / d)

theorem two_mul_div_le (n d : ℕ) : 2 * (n / d) ≤ 2 * n / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [Nat.le_div_iff_mul_le hd]; have := Nat.div_mul_le_self n d; nlinarith

/-- **The carry is `0` or `1`, and it is `1` exactly past the ½ wall**: `2 (n mod d) ≥ d`. -/
theorem carry_eq (n : ℕ) {d : ℕ} (hd : 0 < d) :
    carry n d = if d ≤ 2 * (n % d) then 1 else 0 := by
  have e : 2 * n = d * (2 * (n / d)) + 2 * (n % d) := by
    have := Nat.div_add_mod n d; linarith
  have h2 : 2 * (n % d) < 2 * d := by have := Nat.mod_lt n hd; omega
  unfold carry
  rw [e, Nat.mul_add_div hd]
  split_ifs with h
  · rw [show 2 * (n % d) / d = 1 from Nat.div_eq_of_lt_le (by omega) (by omega)]; omega
  · rw [show 2 * (n % d) / d = 0 from Nat.div_eq_of_lt (by omega)]; omega

theorem carry_le_one (n : ℕ) {d : ℕ} (hd : 0 < d) : carry n d ≤ 1 := by
  rw [carry_eq n hd]; split_ifs <;> omega

/-! ## `q`-integers and `q`-factorials, cyclotomically -/

/-- The `q`-integer `[j]_q = 1 + q + ⋯ + q^{j−1}`. -/
noncomputable def qInt (j : ℕ) : ℤ[X] := ∑ i ∈ range j, X ^ i

/-- The `q`-factorial `[m]_q! = [1]_q [2]_q ⋯ [m]_q`. -/
noncomputable def qFact (m : ℕ) : ℤ[X] := ∏ j ∈ Ioc 0 m, qInt j

/-- `[j]_q = ∏_{d ∣ j, d > 1} Φ_d`. -/
theorem qInt_eq_prod {j : ℕ} (hj : 0 < j) :
    qInt j = ∏ d ∈ j.divisors.erase 1, cyclotomic d ℤ := by
  have h1 : (X - 1 : ℤ[X]) * qInt j = X ^ j - 1 := by rw [qInt, mul_comm, geom_sum_mul]
  have h2 : ∏ d ∈ j.divisors, cyclotomic d ℤ = X ^ j - 1 := prod_cyclotomic_eq_X_pow_sub_one hj ℤ
  rw [← mul_prod_erase _ _ (Nat.one_mem_divisors.mpr hj.ne'), cyclotomic_one] at h2
  have hX : (X - 1 : ℤ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℤ)
  exact mul_left_cancel₀ hX (h1.trans h2.symm)

/-- **`[m]_q! = ∏_{1 < d ≤ m} Φ_d^{⌊m/d⌋}`.** -/
theorem qFact_eq (m : ℕ) : qFact m = ∏ d ∈ Ioc 1 m, cyclotomic d ℤ ^ (m / d) := by
  rw [qFact, prod_congr rfl fun j hj => qInt_eq_prod (mem_Ioc.mp hj).1]
  rw [prod_comm' (t' := Ioc 1 m) (s' := fun d => (Ioc 0 m).filter (d ∣ ·))]
  · refine prod_congr rfl fun d hd => ?_
    rw [prod_const, Nat.Ioc_filter_dvd_card_eq_div]
  · intro j d
    simp only [mem_Ioc, mem_erase, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h0, hm⟩, h1, hdj, -⟩
      have := Nat.le_of_dvd h0 hdj
      have : 0 < d := Nat.pos_of_dvd_of_pos hdj h0
      refine ⟨⟨⟨h0, hm⟩, hdj⟩, ?_, ?_⟩ <;> omega
    · rintro ⟨⟨⟨h0, hm⟩, hdj⟩, h1, -⟩
      exact ⟨⟨h0, hm⟩, by omega, hdj, by omega⟩

/-- **The central `q`-binomial, cyclotomically**: `[2n]_q! = ([n]_q!)² ∏_{1 < d ≤ 2n} Φ_d^{e_d(n)}`,
so `[2n choose n]_q = ∏ Φ_d^{e_d}` with every exponent `0` or `1` (`carry_le_one`). -/
theorem qFact_two_mul (n : ℕ) :
    qFact (2 * n) = qFact n ^ 2 * ∏ d ∈ Ioc 1 (2 * n), cyclotomic d ℤ ^ carry n d := by
  rw [qFact_eq, qFact_eq, ← prod_pow]
  have hsub : Ioc 1 n ⊆ Ioc 1 (2 * n) := Ioc_subset_Ioc_right (by omega)
  rw [prod_subset hsub (f := fun d => (cyclotomic d ℤ ^ (n / d)) ^ 2) (fun d hd hdn => by
    simp only [mem_Ioc, not_and, not_le] at hd hdn
    rw [Nat.div_eq_of_lt (hdn hd.1)]; simp), ← prod_mul_distrib]
  refine prod_congr rfl fun d hd => ?_
  rw [← pow_mul, ← pow_add]
  congr 1
  have := two_mul_div_le n d
  unfold carry; omega

/-! ## At `q = 1`: Kummer and Chebyshev -/

theorem eval_one_qInt (j : ℕ) : (qInt j).eval 1 = j := by simp [qInt]

theorem eval_one_qFact (m : ℕ) : (qFact m).eval 1 = m.factorial := by
  rw [qFact, eval_prod]; simp_rw [eval_one_qInt]
  rw [← Nat.cast_prod, show Ioc 0 m = Ico 1 (m + 1) by ext; simp; omega, prod_Ico_id_eq_factorial]

/-- **`C(2n, n) = ∏_{1 < d ≤ 2n} Φ_d(1)^{e_d(n)}`.** Since `Φ_d(1) = p` for `d = p^k` and `1`
otherwise, this is Kummer's `v_p C(2n, n) = Σ_k e_{p^k}(n)` and Chebyshev's
`log C(2n, n) = Σ_d e_d Λ(d)`. -/
theorem choose_eq_prod_eval (n : ℕ) :
    ((2 * n).choose n : ℤ) = ∏ d ∈ Ioc 1 (2 * n), (cyclotomic d ℤ).eval 1 ^ carry n d := by
  have h := congrArg (eval 1) (qFact_two_mul n)
  rw [eval_mul, eval_pow, eval_prod, eval_one_qFact, eval_one_qFact] at h
  simp_rw [eval_pow] at h
  have hc := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at hc
  have hf : ((n.factorial : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (Nat.factorial_pos n).ne')
  apply mul_left_cancel₀ hf
  rw [← h, ← hc]; push_cast; ring

/-- **`Φ_d(1)`** for `d ≥ 2`: the prime `p` if `d = p^k`, and `1` otherwise. -/
theorem eval_one_cyclotomic_eq {d : ℕ} (hd : 1 < d) :
    (cyclotomic d ℤ).eval 1 = if IsPrimePow d then (d.minFac : ℤ) else 1 := by
  split_ifs with h
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp h
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have := Fact.mk hp
    rw [eval_one_cyclotomic_prime_pow, Nat.Prime.pow_minFac hp (by omega)]
  · rw [eval_one_cyclotomic_not_prime_pow (R := ℤ)]
    intro p hp k hk
    rcases k with _ | k
    · simp at hk; omega
    · exact h ((isPrimePow_nat_iff d).mpr ⟨p, k + 1, hp, by omega, hk⟩)

open ArithmeticFunction in
/-- **`log Φ_d(1) = Λ(d)`** for `d ≥ 2`. -/
theorem log_eval_one_cyclotomic {d : ℕ} (hd : 1 < d) :
    Real.log (((cyclotomic d ℤ).eval 1 : ℤ) : ℝ) = Λ d := by
  rw [eval_one_cyclotomic_eq hd, vonMangoldt_apply]
  split_ifs <;> simp

theorem eval_one_cyclotomic_pos {d : ℕ} (hd : 1 < d) : 0 < (cyclotomic d ℤ).eval 1 := by
  rw [eval_one_cyclotomic_eq hd]
  split_ifs
  · exact_mod_cast Nat.minFac_pos d
  · exact one_pos

open ArithmeticFunction in
/-- **Chebyshev's identity from the cyclotomic factorisation**:
`log C(2n, n) = Σ_{1 < d ≤ 2n} e_d(n) Λ(d)`, each exponent `0` or `1` (the ½ wall). -/
theorem log_choose_eq_sum_carry (n : ℕ) :
    Real.log ((2 * n).choose n) = ∑ d ∈ Ioc 1 (2 * n), (carry n d : ℝ) * Λ d := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (choose_eq_prod_eval n)
  simp only [Int.cast_natCast, Int.cast_prod, Int.cast_pow] at h
  rw [h, Real.log_prod (fun d hd => pow_ne_zero _ (by
    exact_mod_cast (eval_one_cyclotomic_pos (mem_Ioc.mp hd).1).ne'))]
  refine sum_congr rfl fun d hd => ?_
  rw [Real.log_pow, log_eval_one_cyclotomic (mem_Ioc.mp hd).1]

/-- `m! = ∏_{1 < d ≤ m} Φ_d(1)^{⌊m/d⌋}`. -/
theorem factorial_eq_prod_eval (m : ℕ) :
    (m.factorial : ℤ) = ∏ d ∈ Ioc 1 m, (cyclotomic d ℤ).eval 1 ^ (m / d) := by
  have h := congrArg (eval 1) (qFact_eq m)
  rw [eval_one_qFact, eval_prod] at h
  simp_rw [eval_pow] at h
  exact h

open ArithmeticFunction in
/-- **Legendre–Chebyshev for factorials**: `log m! = Σ_{1 < d ≤ m} ⌊m/d⌋ Λ(d)`, the `q = 1` value of
`[m]_q! = ∏ Φ_d^{⌊m/d⌋}`: here the cyclotomic exponents are the quotients `⌊m/d⌋`, not `0/1`
carries. -/
theorem log_factorial_eq_sum (m : ℕ) :
    Real.log (m.factorial) = ∑ d ∈ Ioc 1 m, ((m / d : ℕ) : ℝ) * Λ d := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (factorial_eq_prod_eval m)
  simp only [Int.cast_natCast, Int.cast_prod, Int.cast_pow] at h
  rw [h, Real.log_prod (fun d hd => pow_ne_zero _ (by
    exact_mod_cast (eval_one_cyclotomic_pos (mem_Ioc.mp hd).1).ne'))]
  refine sum_congr rfl fun d hd => ?_
  rw [Real.log_pow, log_eval_one_cyclotomic (mem_Ioc.mp hd).1]

end RMT.Places.Bertrand
