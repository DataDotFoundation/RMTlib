import Mathlib

/-!
# Dehaye–Han, Lemma 12: two properties of `sin`

* Eq. (33): `sin(x − y) sin(x + y) = sin² x − sin² y` (`sin_sub_mul_sin_add`).
* Eq. (34): if `u_1 + ⋯ + u_n = 0` then
  `∏_{i<j} sin(u_i − u_j) = ∏_{i<j} (e^{2u_i I} − e^{2u_j I}) / (2I)` (`prod_sin_sub`).

These are what turn `τ = sin(·z)` into the weight `1 − sin²(tz)/sin²(hz)` and a Vandermonde
determinant in `x_i = e^{2Iz u_i}` (Lemma 13).
-/

open Finset Complex

namespace RMT.MultisetHook

/-- **Eq. (33).** -/
theorem sin_sub_mul_sin_add (x y : ℂ) : sin (x - y) * sin (x + y) = sin x ^ 2 - sin y ^ 2 := by
  rw [sin_sub, sin_add]
  have hx := sin_sq_add_cos_sq x
  have hy := sin_sq_add_cos_sq y
  linear_combination (sin x ^ 2) * hy - (sin y ^ 2) * hx

/-- One factor: `sin(a − b) = e^{−I(a+b)} (e^{2aI} − e^{2bI}) / (2I)`. -/
theorem sin_sub_eq (a b : ℂ) :
    sin (a - b) = exp (-(I * (a + b))) * ((exp (2 * a * I) - exp (2 * b * I)) / (2 * I)) := by
  rw [sin]
  have h1 : exp (-(a - b) * I) = exp (-(I * (a + b))) * exp (2 * b * I) := by
    rw [← exp_add]; ring_nf
  have h2 : exp ((a - b) * I) = exp (-(I * (a + b))) * exp (2 * a * I) := by
    rw [← exp_add]; ring_nf
  rw [h1, h2]
  field_simp
  ring_nf
  rw [I_sq]; ring

/-- `∑_{i<j} (u_i + u_j) = (n − 1) ∑ u`. -/
theorem sum_pairs_fin {n : ℕ} (u : Fin n → ℂ) :
    ∑ i, ∑ j ∈ Ioi i, (u i + u j) = ((n : ℂ) - 1) * ∑ i, u i := by
  have h1 : ∑ i, ∑ j ∈ Ioi i, u i = ∑ i : Fin n, ((n - 1 - i : ℕ) : ℂ) * u i := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_const, Fin.card_Ioi, nsmul_eq_mul]
  have h2 : ∑ i, ∑ j ∈ Ioi i, u j = ∑ j : Fin n, ((j : ℕ) : ℂ) * u j := by
    rw [sum_comm' (t' := univ) (s' := fun j => Iio j)]
    · refine sum_congr rfl fun j _ => ?_
      rw [sum_const, Fin.card_Iio, nsmul_eq_mul]
    · intro i j; simp
  simp only [sum_add_distrib]
  rw [h1, h2, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have := i.isLt
  push_cast [Nat.cast_sub (show (i : ℕ) ≤ n - 1 by omega), Nat.cast_sub (show 1 ≤ n by omega)]
  ring

/-- **Eq. (34).** -/
theorem prod_sin_sub {n : ℕ} (u : Fin n → ℂ) (hu : ∑ i, u i = 0) :
    ∏ i, ∏ j ∈ Ioi i, sin (u i - u j) =
      ∏ i, ∏ j ∈ Ioi i, (exp (2 * u i * I) - exp (2 * u j * I)) / (2 * I) := by
  simp only [sin_sub_eq, prod_mul_distrib]
  have e : ∏ i, ∏ j ∈ Ioi i, exp (-(I * (u i + u j))) =
      exp (∑ i, ∑ j ∈ Ioi i, -(I * (u i + u j))) := by simp only [Complex.exp_sum]
  have e2 : ∑ i, ∑ j ∈ Ioi i, -(I * (u i + u j)) = -(I * ∑ i, ∑ j ∈ Ioi i, (u i + u j)) := by
    simp only [sum_neg_distrib, mul_sum]
  have : ∏ i, ∏ j ∈ Ioi i, exp (-(I * (u i + u j))) = 1 := by
    rw [e, e2, sum_pairs_fin, hu, mul_zero, mul_zero, neg_zero, exp_zero]
  rw [this, one_mul]

end RMT.MultisetHook
