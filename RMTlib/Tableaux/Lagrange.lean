import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination

/-!
# The Lagrange identity

For distinct `x₁, …, x_N`,
`Σ_i x_i ∏_{j≠i} (x_i − x_j − 1)/(x_i − x_j) = Σ_i x_i − N(N−1)/2`.

This is the identity behind the branching step of the hook-length formula: in Frobenius
coordinates `ℓ_i = ν_i + N − i`, removing a corner from row `i` replaces `ℓ_i` by `ℓ_i − 1`.

Proof: with `P = ∏(X − x_j)` and `Q = ∏(X − x_j − 1)`, the polynomial `R = X(Q − P) + N·P` has
degree `< N` and `R(x_i) = −x_i ∏_{j≠i}(x_i − x_j − 1)`. Lagrange interpolation
(`Lagrange.coeff_eq_sum`) reads its `X^{N−1}` coefficient off these values; the coefficient itself
comes from the top three coefficients of `P` and `Q` (`top_three`). This is the residue theorem
at infinity for `z ∏_j (z − x_j − 1)/(z − x_j)`, done with polynomials.
-/

open Finset Polynomial
open scoped Nat

namespace RMT.Lagrange

variable {ι : Type*} [DecidableEq ι]

/-- Top three coefficients of `∏ (X − a_j)`, in a form free of natural subtraction:
`2 X² ∏_{j∈s}(X − a_j) = 2X^{n+2} − 2 p₁ X^{n+1} + (p₁² − p₂) X^n + (lower)`. -/
theorem top_three (s : Finset ι) (a : ι → ℚ) :
    ∃ r : ℚ[X], r.degree < #s ∧
      2 * X ^ 2 * ∏ j ∈ s, (X - C (a j)) =
        2 * X ^ (#s + 2) - 2 * C (∑ j ∈ s, a j) * X ^ (#s + 1) +
          C ((∑ j ∈ s, a j) ^ 2 - ∑ j ∈ s, a j ^ 2) * X ^ #s + r := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert b s hb ih =>
    obtain ⟨r, hr, h⟩ := ih
    refine ⟨C (-(a b * ((∑ j ∈ s, a j) ^ 2 - ∑ j ∈ s, a j ^ 2))) * X ^ #s
        + (X - C (a b)) * r, ?_, ?_⟩
    · rw [card_insert_of_notMem hb]
      refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
      · exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast Nat.lt_succ_self _)
      · rw [degree_mul, degree_X_sub_C]
        by_cases r0 : r = 0
        · simp [r0]
        · rw [degree_eq_natDegree r0] at hr ⊢
          have : r.natDegree < #s := by exact_mod_cast hr
          rw [add_comm]; exact_mod_cast (by omega : r.natDegree + 1 < #s + 1)
    · rw [prod_insert hb, sum_insert hb, sum_insert hb, card_insert_of_notMem hb]
      simp only [map_add, map_sub, map_pow, map_mul, map_neg] at h ⊢
      linear_combination (X - C (a b)) * h


theorem coeff_two_X_sq_mul (R : ℚ[X]) (k : ℕ) : (2 * X ^ 2 * R).coeff (k + 2) = 2 * R.coeff k := by
  rw [show (2 : ℚ[X]) * X ^ 2 * R = C 2 * (R * X ^ 2) by rw [C_ofNat]; ring, coeff_C_mul,
    coeff_mul_X_pow]

theorem lagrange_identity (N : ℕ) (x : Fin N → ℚ) (hx : Function.Injective x) :
    ∑ i, x i * ∏ j ∈ univ.erase i, (x i - x j - 1) / (x i - x j) =
      ∑ i, x i - (N * (N - 1) / 2 : ℕ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set p := ∑ j, x j with hp
  set P : ℚ[X] := ∏ j, (X - C (x j)) with hPdef
  set Q : ℚ[X] := ∏ j, (X - C (x j + 1)) with hQdef
  set R : ℚ[X] := X * (Q - P) + (N : ℚ[X]) * P with hRdef
  obtain ⟨rP, hrP, hP⟩ := top_three (univ : Finset (Fin N)) x
  obtain ⟨rQ, hrQ, hQ⟩ := top_three (univ : Finset (Fin N)) (fun j => x j + 1)
  rw [← hPdef, ← hp] at hP
  rw [← hQdef] at hQ
  simp only [card_univ, Fintype.card_fin] at hrP hrQ hP hQ
  have h1 : ∑ j, (x j + 1) = p + N := by simp [sum_add_distrib, hp]
  have h2 : ∑ j, (x j + 1) ^ 2 = ∑ j, x j ^ 2 + 2 * p + N := by
    simp only [add_sq, sum_add_distrib, mul_one, one_pow, ← mul_sum, hp]; simp
  rw [h1, h2] at hQ
  -- the expansion of `2 X² R`
  set t : ℚ[X] := X * (rQ - rP) + (N : ℚ[X]) * (C (p ^ 2 - ∑ j, x j ^ 2) * X ^ N + rP) with ht
  have key : 2 * X ^ 2 * R = C ((N : ℚ) ^ 2 - N - 2 * p) * X ^ (N + 1) + t := by
    rw [hRdef, ht]
    simp only [map_add, map_sub, map_pow, map_mul, map_natCast, map_ofNat] at hP hQ ⊢
    linear_combination X * (hQ - hP) + (N : ℚ[X]) * hP
  have htdeg : t.degree < (N + 1 : ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [ht, coeff_add, coeff_X_mul, coeff_natCast_mul, coeff_add, coeff_C_mul_X_pow, coeff_sub,
      if_neg (by omega), coeff_eq_zero_of_degree_lt (hrQ.trans_le (by exact_mod_cast (by omega))),
      coeff_eq_zero_of_degree_lt (hrP.trans_le (by exact_mod_cast (by omega))),
      coeff_eq_zero_of_degree_lt (hrP.trans_le (by exact_mod_cast (by omega)))]
    simp
  have hcoeff : ∀ k, R.coeff k * 2 =
      (if k + 2 = N + 1 then (N : ℚ) ^ 2 - N - 2 * p else 0) + t.coeff (k + 2) := by
    intro k
    rw [mul_comm, ← coeff_two_X_sq_mul, key, coeff_add, coeff_C_mul_X_pow]
  have hRdeg : R.degree < #(univ : Finset (Fin N)) := by
    rw [card_univ, Fintype.card_fin, degree_lt_iff_coeff_zero]
    intro k hk
    have := hcoeff k
    rw [if_neg (by omega), coeff_eq_zero_of_degree_lt
      (htdeg.trans_le (by exact_mod_cast (by omega : N + 1 ≤ k + 2))), add_zero] at this
    simpa using this
  have hsum := Lagrange.coeff_eq_sum (s := univ) (v := x) (hx.injOn) hRdeg
  rw [card_univ, Fintype.card_fin] at hsum
  have htop : R.coeff (N - 1) * 2 = (N : ℚ) ^ 2 - N - 2 * p := by
    rw [hcoeff, if_pos (by omega), coeff_eq_zero_of_degree_lt
      (htdeg.trans_le (by exact_mod_cast (by omega : N + 1 ≤ N - 1 + 2))), add_zero]
  have heval : ∀ i, R.eval (x i) = -(x i * ∏ j ∈ univ.erase i, (x i - x j - 1)) := by
    intro i
    have hP0 : P.eval (x i) = 0 := by
      rw [hPdef, eval_prod]; exact prod_eq_zero (mem_univ i) (by simp)
    have hQi : Q.eval (x i) = -∏ j ∈ univ.erase i, (x i - x j - 1) := by
      rw [hQdef, eval_prod, ← mul_prod_erase univ _ (mem_univ i)]
      simp only [eval_sub, eval_X, eval_C]
      rw [show x i - (x i + 1) = -1 by ring, neg_one_mul]
      congr 1; refine prod_congr rfl fun j _ => by ring
    simp only [hRdef, eval_add, eval_mul, eval_X, eval_sub, hP0, hQi, eval_natCast]
    ring
  simp only [heval] at hsum
  have hlhs : ∑ i, x i * ∏ j ∈ univ.erase i, (x i - x j - 1) / (x i - x j) =
      -∑ i, -(x i * ∏ j ∈ univ.erase i, (x i - x j - 1)) / ∏ j ∈ univ.erase i, (x i - x j) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [prod_div_distrib]; ring
  rw [hlhs, ← hsum, ← Nat.choose_two_right, Nat.cast_choose_two]
  linear_combination (-1 / 2 : ℚ) * htop

end RMT.Lagrange
