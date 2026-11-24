import RMTlib.Symmetric.WeightedCauchy
import RMTlib.Tableaux.Hooks
import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Corners: content products and hook products as charges on the content axis

In Russian notation the profile of a partition `λ` has minima `x_0 < ⋯ < x_d` (the contents of
its addable cells) and maxima `y_1 < ⋯ < y_d` (the contents of its removable cells). Give the
minima charge `+1` and the maxima charge `−1`; the total charge is `+1`. With `G` the Barnes
function at integers (`barnesG`, `G(n) = ∏_{k<n−1} k!`) and `log G(1 + |·|)` the discrete Green's
function of the second difference (`G(x+2) G(x) / G(x+1)² = x`), two identities hold:

* **(C)** `∏_{□ ∈ λ} (N + c(□)) = ∏_{corners u} G(N + 1 + u)^{ε_u} / G(N + 1)`
  (`contentProdP_corners_barnesG`);
* **(H)** `H(λ) = ∏_{corners u < v} G(1 + |u − v|)^{ε_u ε_v}` (`hookProd_corners`).

## The charge, through the Maya diagram

For `ν : Fin N → ℕ` (a partition with at most `N` rows) the Maya positions are
`b_i = ν_i − i − 1` (`maya`). The charge is `charge ν = ∑_i (δ_{b_i + 1} − δ_{b_i}) + δ_{−N}`
(`charge`): **each row is a `±` dipole of unit width**, and the boundary at `−N` (the first row
not used) carries the external charge `+1`. Adjacent dipoles (equal rows) cancel, and what is left
is the corner measure: `+1` at the content `ν_i − i` of the addable cell of row `i` (when row `i`
is addable), `−1` at the content `ν_i − i − 1` of the removable cell, `+1` at `−N`. The identities
are stated with this charge on the window `[−N, M]` (`window`), `M ≥ ν_0`, which contains its
support.

## Results

* `prod_charge`, `sum_charge`: **summation by parts.** `∏_u g(u)^{charge(u)} =
  ∏_i g(b_i + 1)/g(b_i) · g(−N)`: a product against the corners is a product of first differences
  over the rows.
* `contentProdP_mul_corners`: **the uniform corner statement.** For any content function `f` and
  any potential `Φ` whose discrete second difference is `f`
  (`Φ(c+1) Φ(c−1) = f(c) Φ(c)²`), `contentProdP f ν · Φ(0) = ∏_u Φ(u)^{charge(u)}`. The proof is a
  telescoping product, row by row. At `f = N + c`, `Φ = G(N + 1 + ·)` it is (C); at constant
  content `T`, `Φ(u) = T^{u(u+1)/2}` it is `T^{|λ|}` (`contentProdP_const_corners`).
* `contentProdP_corners_barnesG`: (C).
* `hookProd_corners`, `hookProd_sq_corners`: (H), from the bilinear expansion of the dipoles and
  Frobenius's identity (`RMT.frobenius`).

Conjugation reflects the profile, `u ↦ −u`; on (C) it is `N ↦ −N`, which is
`RMT.Symmetric.contentProd_transpose` (`∏_{λᵀ} (N + c) = ∏_λ (N − c)`).
-/

open Finset
open scoped Nat

noncomputable section

namespace RMT.Symmetric.Corners

/-! ## Barnes `G` at integers -/

/-- Barnes `G` at positive integers, `G(n) = ∏_{k < n − 1} k!`: Mathlib's superfactorial shifted
by two, `G(n + 2) = Nat.superFactorial n`, with `G(1) = G(2) = 1` (and the junk value `G(0) = 1`). -/
def barnesG (n : ℕ) : ℕ := Nat.superFactorial (n - 2)

theorem barnesG_succ_succ (n : ℕ) : barnesG (n + 2) = n ! * barnesG (n + 1) := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [barnesG, show n + 1 + 2 - 2 = n + 1 by omega, show n + 1 + 1 - 2 = n by omega]
    exact Nat.superFactorial_succ n

theorem barnesG_pos (n : ℕ) : 0 < barnesG n := by
  suffices h : ∀ k, 0 < Nat.superFactorial k from h _
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.superFactorial_succ]; exact Nat.mul_pos (Nat.factorial_pos _) ih

/-- `G(n + 2) G(n) = n G(n + 1)²` for `n ≥ 1`: `log G(1 + |·|)` has second difference `log |·|`. -/
theorem barnesG_rec (n : ℕ) (hn : 1 ≤ n) :
    barnesG (n + 2) * barnesG n = n * barnesG (n + 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [barnesG_succ_succ, show m + 1 + 1 = m + 2 by ring, barnesG_succ_succ m, Nat.factorial_succ]
  ring

/-! ## Maya positions and the charge -/

variable {N : ℕ}

/-- The Maya position of row `i`: `b_i = ν_i − i − 1`. -/
def maya (ν : Fin N → ℕ) (i : Fin N) : ℤ := (ν i : ℤ) - i - 1

/-- The set of Maya positions. -/
def mayaSet (ν : Fin N → ℕ) : Finset ℤ := univ.image (maya ν)

/-- **The corner charge**: `∑_i (δ_{b_i + 1} − δ_{b_i}) + δ_{−N}`. -/
def charge (ν : Fin N → ℕ) (u : ℤ) : ℤ :=
  (if u - 1 ∈ mayaSet ν then 1 else 0) - (if u ∈ mayaSet ν then 1 else 0) +
    (if u = -(N : ℤ) then 1 else 0)

/-- The window `[−N, M]`, which contains the support of the charge when `ν ≤ M`. -/
def window (N M : ℕ) : Finset ℤ := Icc (-(N : ℤ)) M

theorem maya_strictAnti {ν : Fin N → ℕ} (hν : Antitone ν) {i j : Fin N} (h : i < j) :
    maya ν j < maya ν i := by
  have := hν h.le
  have : (i : ℕ) < j := h
  unfold maya; omega

theorem maya_injective {ν : Fin N → ℕ} (hν : Antitone ν) : Function.Injective (maya ν) := by
  intro i j h
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd h (maya_strictAnti hν hij).ne'
  · rfl
  · exact absurd h (maya_strictAnti hν hij).ne

variable {M : ℕ}

theorem maya_mem {ν : Fin N → ℕ} (hM : ∀ i, ν i ≤ M) (i : Fin N) : maya ν i ∈ window N M := by
  have := hM i; have := i.isLt
  simp only [window, mem_Icc, maya]; omega

theorem maya_succ_mem {ν : Fin N → ℕ} (hM : ∀ i, ν i ≤ M) (i : Fin N) :
    maya ν i + 1 ∈ window N M := by
  have := hM i; have := i.isLt
  simp only [window, mem_Icc, maya]; omega

theorem neg_mem_window : -(N : ℤ) ∈ window N M := by simp [window]

theorem zero_mem_window : (0 : ℤ) ∈ window N M := by simp [window]

/-! ## Summation by parts -/

section Field

variable {K : Type*} [Field K]

/-- **Summation by parts.** A product against the corner charge is a product of first differences
over the rows: `∏_u g(u)^{charge(u)} = ∏_i g(b_i + 1)/g(b_i) · g(−N)`. -/
theorem prod_charge {ν : Fin N → ℕ} (hν : Antitone ν) (hM : ∀ i, ν i ≤ M) (g : ℤ → K)
    (hg : ∀ u ∈ window N M, g u ≠ 0) :
    ∏ u ∈ window N M, g u ^ charge ν u =
      (∏ i, g (maya ν i + 1) / g (maya ν i)) * g (-(N : ℤ)) := by
  have hpow : ∀ u ∈ window N M, g u ^ charge ν u =
      (if u - 1 ∈ mayaSet ν then g u else 1) * (if u ∈ mayaSet ν then g u else 1)⁻¹ *
        (if u = -(N : ℤ) then g u else 1) := by
    intro u hu
    unfold charge
    rw [zpow_add₀ (hg u hu), zpow_sub₀ (hg u hu)]
    split_ifs <;> simp [div_eq_mul_inv]
  rw [prod_congr rfl hpow, prod_mul_distrib, prod_mul_distrib, prod_inv_distrib, ← prod_filter,
    ← prod_filter, ← prod_filter]
  have e1 : (window N M).filter (fun u => u - 1 ∈ mayaSet ν) =
      univ.image (fun i => maya ν i + 1) := by
    ext u
    simp only [mem_filter, mayaSet, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨-, i, hi⟩; exact ⟨i, by omega⟩
    · rintro ⟨i, rfl⟩; exact ⟨maya_succ_mem hM i, i, by ring⟩
  have e2 : (window N M).filter (fun u => u ∈ mayaSet ν) = univ.image (maya ν) := by
    ext u
    simp only [mem_filter, mayaSet, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨i, rfl⟩; exact ⟨maya_mem hM i, i, rfl⟩
  have e3 : (window N M).filter (fun u => u = -(N : ℤ)) = {-(N : ℤ)} := by
    ext u; simp only [mem_filter, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨neg_mem_window, rfl⟩
  rw [e1, e2, e3, prod_singleton,
    prod_image fun i _ j _ h => maya_injective hν (by simpa using h),
    prod_image fun i _ j _ h => maya_injective hν h, prod_div_distrib, div_eq_mul_inv]

/-- The content product of `ν : Fin N → ℕ`, row by row. -/
theorem contentProdP_ofFn (f : ℤ → K) (ν : Fin N → ℕ) :
    contentProdP f (List.ofFn ν) = ∏ i : Fin N, ∏ c ∈ range (ν i), f ((c : ℤ) - i) := by
  rw [contentProdP, List.length_ofFn,
    prod_range (fun i => ∏ j ∈ range ((List.ofFn ν).getD i 0), f ((j : ℤ) - i))]
  refine prod_congr rfl fun i _ => ?_
  have hg : (List.ofFn ν).getD i 0 = ν i := by simp [List.getD_eq_getElem?_getD]
  rw [hg]

/-- **The uniform corner statement.** If the potential `Φ` has discrete second difference `f`
on the window (`Φ(c+1) Φ(c−1) = f(c) Φ(c)²`) and does not vanish there, then
`contentProdP f ν · Φ(0) = ∏_u Φ(u)^{charge(u)}`. Each row telescopes: the first difference
`D(w) = Φ(w)/Φ(w−1)` is multiplied by `f(w)` at each step, so
`D(ν_i − i) = D(−i) ∏_{c<ν_i} f(c − i)`. -/
theorem contentProdP_mul_corners {ν : Fin N → ℕ} (hν : Antitone ν) (hM : ∀ i, ν i ≤ M)
    (f Φ : ℤ → K) (hΦ : ∀ u ∈ window N M, Φ u ≠ 0)
    (hrec : ∀ c : ℤ, -(N : ℤ) < c → c < M → Φ (c + 1) * Φ (c - 1) = f c * Φ c ^ 2) :
    contentProdP f (List.ofFn ν) * Φ 0 = ∏ u ∈ window N M, Φ u ^ charge ν u := by
  have mem : ∀ u : ℤ, -(N : ℤ) ≤ u → u ≤ M → Φ u ≠ 0 := fun u h1 h2 =>
    hΦ u (by simp [window]; omega)
  rw [prod_charge hν hM Φ hΦ, contentProdP_ofFn]
  -- one row
  have row : ∀ i : Fin N, ∀ n : ℕ, n ≤ ν i →
      Φ ((n : ℤ) - i) / Φ ((n : ℤ) - i - 1) =
        Φ (-(i : ℤ)) / Φ (-(i : ℤ) - 1) * ∏ c ∈ range n, f ((c : ℤ) - i) := by
    intro i n hn
    have hi := i.isLt; have hνi := hM i
    induction n with
    | zero => simp
    | succ n ih =>
      rw [prod_range_succ, ← mul_assoc, ← ih (by omega)]
      have h := hrec ((n : ℤ) - i) (by omega) (by omega)
      have a := mem ((n : ℤ) - i) (by omega) (by omega)
      have b := mem ((n : ℤ) - i - 1) (by omega) (by omega)
      push_cast
      rw [show (n : ℤ) + 1 - i = (n - i) + 1 by ring, show (n : ℤ) - i + 1 - 1 = n - i by ring]
      field_simp
      linear_combination h
  -- the vacuum telescopes to `Φ(0)/Φ(−N)`
  have vac : ∀ n : ℕ, n ≤ N →
      (∏ i ∈ range n, Φ (-(i : ℤ)) / Φ (-(i : ℤ) - 1)) * Φ (-(n : ℤ)) = Φ 0 := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [prod_range_succ, mul_assoc, ← ih (by omega)]
      have := mem (-(n : ℤ) - 1) (by omega) (by omega)
      push_cast
      rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring]
      field_simp
  have hrows : ∏ i : Fin N, Φ (maya ν i + 1) / Φ (maya ν i) =
      (∏ i : Fin N, Φ (-(i : ℤ)) / Φ (-(i : ℤ) - 1)) *
        ∏ i : Fin N, ∏ c ∈ range (ν i), f ((c : ℤ) - i) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [← row i (ν i) le_rfl, maya, show (ν i : ℤ) - i - 1 + 1 = ν i - i by ring]
  have vacF : (∏ i : Fin N, Φ (-(i : ℤ)) / Φ (-(i : ℤ) - 1)) * Φ (-(N : ℤ)) = Φ 0 := by
    rw [Fin.prod_univ_eq_prod_range (fun i => Φ (-(i : ℤ)) / Φ (-(i : ℤ) - 1)) N]
    exact vac N le_rfl
  rw [hrows, ← vacF]
  ring

/-- The Barnes potential has second difference `N + c`:
`G(N + 2 + c) G(N + c) = (N + c) G(N + 1 + c)²` for `c > −N`. -/
theorem barnesG_potential_rec (N : ℕ) (c : ℤ) (hc : -(N : ℤ) < c) :
    ((barnesG ((N : ℤ) + 1 + (c + 1)).toNat : ℕ) : K) * ((barnesG ((N : ℤ) + 1 + (c - 1)).toNat : ℕ) : K)
      = ((N : K) + c) * ((barnesG ((N : ℤ) + 1 + c).toNat : ℕ) : K) ^ 2 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = N + c := ⟨(N + c).toNat, Int.toNat_of_nonneg (by omega)⟩
  have e1 : ((N : ℤ) + 1 + (c + 1)).toNat = n + 2 := by omega
  have e2 : ((N : ℤ) + 1 + (c - 1)).toNat = n := by omega
  have e3 : ((N : ℤ) + 1 + c).toNat = n + 1 := by omega
  rw [e1, e2, e3]
  have := barnesG_rec n (by omega)
  have hc' : ((N : K) + c) = n := by
    have := congrArg (Int.cast (R := K)) hn
    push_cast at this; exact this.symm
  rw [hc']
  have h := congrArg (Nat.cast (R := K)) this
  push_cast at h; exact h

/-- **(C) The content product `∏ (N + c)` against the corners**:
`∏_{□} (N + c(□)) · G(N + 1) = ∏_u G(N + 1 + u)^{charge(u)}`. -/
theorem contentProdP_corners_barnesG [CharZero K] {ν : Fin N → ℕ} (hν : Antitone ν)
    (hM : ∀ i, ν i ≤ M) :
    contentProdP (fun c : ℤ => (N : K) + c) (List.ofFn ν) * barnesG (N + 1) =
      ∏ u ∈ window N M, ((barnesG (N + 1 + u).toNat : ℕ) : K) ^ charge ν u := by
  have h := contentProdP_mul_corners hν hM (fun c : ℤ => (N : K) + c)
    (fun u => ((barnesG (N + 1 + u).toNat : ℕ) : K))
    (fun u _ => by exact_mod_cast (barnesG_pos _).ne') (fun c h1 _ => barnesG_potential_rec N c h1)
  simpa using h

/-- The Gaussian potential `T^{u(u+1)/2}` has constant second difference `T`. -/
theorem const_potential_rec (T : K) (c : ℤ) :
    T ^ ((c + 1) * (c + 1 + 1) / 2).toNat * T ^ ((c - 1) * (c - 1 + 1) / 2).toNat =
      T * (T ^ (c * (c + 1) / 2).toNat) ^ 2 := by
  rw [← pow_mul, ← pow_add, ← pow_succ']
  congr 1
  have h1 : (c + 1) * (c + 1 + 1) / 2 = c * (c + 1) / 2 + (c + 1) := by
    rw [show (c + 1) * (c + 1 + 1) = c * (c + 1) + 2 * (c + 1) by ring,
      Int.add_mul_ediv_left _ _ two_ne_zero]
  have h2 : c * (c + 1) / 2 = (c - 1) * (c - 1 + 1) / 2 + c := by
    rw [show c * (c + 1) = (c - 1) * (c - 1 + 1) + 2 * c by ring,
      Int.add_mul_ediv_left _ _ two_ne_zero]
  have h0 : ∀ z : ℤ, 0 ≤ z * (z + 1) / 2 := fun z => by
    apply Int.ediv_nonneg _ (by norm_num)
    rcases le_or_gt 0 z with hz | hz
    · positivity
    · nlinarith
  have := h0 c; have := h0 (c - 1); have := h0 (c + 1)
  generalize (c + 1) * (c + 1 + 1) / 2 = A at *
  generalize (c - 1) * (c - 1 + 1) / 2 = B at *
  generalize c * (c + 1) / 2 = X at *
  omega

/-- At a finite place: constant content `T`, potential `T^{u(u+1)/2}`. The corner statement is
`T^{|λ|} = ∏_u (T^{u(u+1)/2})^{charge(u)}`, i.e. `|λ| = ∑_u charge(u) · u(u+1)/2`. -/
theorem contentProdP_const_corners {ν : Fin N → ℕ} (hν : Antitone ν) (hM : ∀ i, ν i ≤ M)
    (T : K) (hT : T ≠ 0) :
    contentProdP (fun _ : ℤ => T) (List.ofFn ν) =
      ∏ u ∈ window N M, (T ^ (u * (u + 1) / 2).toNat) ^ charge ν u := by
  have h := contentProdP_mul_corners hν hM (fun _ : ℤ => T) (fun u => T ^ (u * (u + 1) / 2).toNat)
    (fun u _ => pow_ne_zero _ hT) (fun c _ _ => const_potential_rec T c)
  simpa using h

end Field

/-! ## (H): the hook product against the corners -/

section Hook

/-- The kernel `K(d) = log G(1 + |d|)`. -/
noncomputable def kern (d : ℤ) : ℝ := Real.log (barnesG (1 + |d|).toNat)

theorem kern_neg (d : ℤ) : kern (-d) = kern d := by simp [kern]

theorem kern_zero : kern 0 = 0 := by simp [kern, barnesG]

/-- First differences: `K(w + 1) − K(w) = log w!` for `w ≥ 0`. -/
theorem kern_succ_sub (w : ℤ) (hw : 0 ≤ w) : kern (w + 1) - kern w = Real.log (w.toNat)! := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = n := ⟨w.toNat, (Int.toNat_of_nonneg hw).symm⟩
  have e1 : (1 + |(n : ℤ) + 1|).toNat = n + 2 := by rw [abs_of_nonneg (by omega)]; omega
  have e2 : (1 + |(n : ℤ)|).toNat = n + 1 := by rw [abs_of_nonneg (by omega)]; omega
  rw [kern, kern, e1, e2, barnesG_succ_succ, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (Nat.factorial_pos _).ne') (by exact_mod_cast (barnesG_pos _).ne')]
  simp

/-- Second differences: `K(d + 1) + K(d − 1) − 2 K(d) = log |d|` (both sides `0` at `d = 0`). -/
theorem kern_second (d : ℤ) : kern (d + 1) + kern (d - 1) - 2 * kern d = Real.log |(d : ℝ)| := by
  have pos : ∀ d : ℕ, 1 ≤ d → kern ((d : ℤ) + 1) + kern ((d : ℤ) - 1) - 2 * kern d =
      Real.log (d : ℝ) := by
    intro d hd
    have e1 : (1 + |(d : ℤ) + 1|).toNat = d + 2 := by rw [abs_of_nonneg (by omega)]; omega
    have e2 : (1 + |(d : ℤ) - 1|).toNat = d := by rw [abs_of_nonneg (by omega)]; omega
    have e3 : (1 + |(d : ℤ)|).toNat = d + 1 := by rw [abs_of_nonneg (by omega)]; omega
    rw [kern, kern, kern, e1, e2, e3]
    have h := congrArg (Nat.cast (R := ℝ)) (barnesG_rec d hd)
    push_cast at h
    have g1 : (0 : ℝ) < barnesG (d + 2) := by exact_mod_cast barnesG_pos _
    have g2 : (0 : ℝ) < barnesG d := by exact_mod_cast barnesG_pos _
    have g3 : (0 : ℝ) < barnesG (d + 1) := by exact_mod_cast barnesG_pos _
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have := congrArg Real.log h
    rw [Real.log_mul g1.ne' g2.ne', Real.log_mul hd'.ne' (by positivity), Real.log_pow] at this
    push_cast at this ⊢
    linarith
  rcases lt_trichotomy d 0 with h | rfl | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, -d = n := ⟨(-d).toNat, by omega⟩
    have := pos n (by omega)
    rw [show d + 1 = -((n : ℤ) - 1) by omega, show d - 1 = -((n : ℤ) + 1) by omega,
      show d = -(n : ℤ) by omega, kern_neg, kern_neg, kern_neg]
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
    linarith
  · simp only [zero_add, zero_sub, kern_neg, kern_zero, Int.cast_zero, abs_zero, Real.log_zero]
    have := kern_succ_sub 0 le_rfl
    simp only [zero_add, kern_zero, Int.toNat_zero, Nat.factorial_zero, Nat.cast_one,
      Real.log_one, sub_zero] at this
    linarith
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n := ⟨d.toNat, by omega⟩
    rw [pos n (by omega)]
    push_cast
    rw [abs_of_nonneg (by positivity)]

/-- A symmetric double sum with zero diagonal is twice the sum over `x < y`. -/
theorem sum_sum_eq_two_mul {α : Type*} [LinearOrder α] (s : Finset α) (f : α → α → ℝ)
    (hsymm : ∀ x y, f x y = f y x) (hdiag : ∀ x, f x x = 0) :
    ∑ x ∈ s, ∑ y ∈ s, f x y = 2 * ∑ x ∈ s, ∑ y ∈ s.filter (x < ·), f x y := by
  have h1 : ∀ x ∈ s, ∑ y ∈ s, f x y =
      ∑ y ∈ s.filter (x < ·), f x y + ∑ y ∈ s.filter (· < x), f x y := by
    intro x _
    rw [← sum_filter_add_sum_filter_not s (x < ·)]
    congr 1
    rw [← sum_filter_add_sum_filter_not (s.filter fun y => ¬ x < y) (· < x)]
    have a : (s.filter fun y => ¬ x < y).filter (· < x) = s.filter (· < x) := by
      ext y; simp only [mem_filter]; constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · exact fun h => ⟨⟨h.1, not_lt.mpr h.2.le⟩, h.2⟩
    rw [a, sum_eq_zero (s := (s.filter fun y => ¬ x < y).filter fun y => ¬ y < x), add_zero]
    intro y hy
    simp only [mem_filter, not_lt] at hy
    rw [le_antisymm hy.1.2 hy.2, hdiag]
  rw [sum_congr rfl h1, sum_add_distrib, two_mul]
  congr 1
  rw [sum_comm' (t' := s) (s' := fun y => s.filter (y < ·))]
  · exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => hsymm _ _
  · intro x y; simp only [mem_filter]; tauto

variable {ν : Fin N → ℕ}

/-- **Summation by parts, additively.** `∑_u charge(u) F(u) = ∑_i (F(b_i + 1) − F(b_i)) + F(−N)`. -/
theorem sum_charge (hν : Antitone ν) (hM : ∀ i, ν i ≤ M) (F : ℤ → ℝ) :
    ∑ u ∈ window N M, (charge ν u : ℝ) * F u =
      ∑ i, (F (maya ν i + 1) - F (maya ν i)) + F (-(N : ℤ)) := by
  have h := congrArg Real.log (prod_charge hν hM (fun u => Real.exp (F u)) fun u _ =>
    (Real.exp_pos _).ne')
  rw [Real.log_prod (fun u _ => (zpow_pos (Real.exp_pos _) _).ne'),
    Real.log_mul (prod_ne_zero_iff.mpr fun i _ => (div_pos (Real.exp_pos _) (Real.exp_pos _)).ne')
      (Real.exp_pos _).ne',
    Real.log_prod (fun i _ => (div_pos (Real.exp_pos _) (Real.exp_pos _)).ne'), Real.log_exp] at h
  simp only [Real.log_zpow, Real.log_exp, Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne'] at h
  exact h

/-- Frobenius's identity in logarithms, in Maya coordinates:
`log H(ν) = ∑_i log (b_i + N)! − ∑_{i<j} log (b_i − b_j)`. -/
theorem log_hookProd (hν : Antitone ν) :
    Real.log (RMT.hookProd ν) = ∑ i, Real.log ((maya ν i + N).toNat)! -
      ∑ i, ∑ j ∈ univ.filter (i < ·), Real.log ((maya ν i - maya ν j : ℤ) : ℝ) := by
  have hf := congrArg (Nat.cast (R := ℝ)) (RMT.frobenius ν hν)
  simp only [Nat.cast_mul, Nat.cast_prod] at hf
  have hH : (0 : ℝ) < RMT.hookProd ν := by
    have h := RMT.frobenius ν hν
    rcases Nat.eq_zero_or_pos (RMT.hookProd ν) with h0 | h0
    · rw [h0, zero_mul] at h
      exact absurd h.symm (prod_pos fun _ _ => Nat.factorial_pos _).ne'
    · exact_mod_cast h0
  have hV : ∀ i : Fin N, ∀ j ∈ Ioi i,
      (((ν i - ν j + (j - i) : ℕ) : ℝ)) = ((maya ν i - maya ν j : ℤ) : ℝ) := by
    intro i j hj
    have hij : (i : ℕ) < j := Fin.lt_def.mp (mem_Ioi.mp hj)
    have := hν hij.le
    unfold maya
    push_cast [Nat.cast_sub this, Nat.cast_sub hij.le]
    ring
  have hVpos : ∀ i : Fin N, ∀ j ∈ Ioi i, (0 : ℝ) < ((maya ν i - maya ν j : ℤ) : ℝ) := by
    intro i j hj
    have := maya_strictAnti hν (mem_Ioi.mp hj)
    exact_mod_cast (by omega : (0 : ℤ) < maya ν i - maya ν j)
  have hfac : ∀ i : Fin N, (((ν i + (N - 1 - i))! : ℕ) : ℝ) = (((maya ν i + N).toNat)! : ℕ) := by
    intro i
    have := i.isLt
    congr 2
    unfold maya; omega
  rw [prod_congr rfl fun i _ => prod_congr rfl fun j hj => hV i j hj,
    prod_congr rfl fun i _ => hfac i] at hf
  have hl := congrArg Real.log hf
  rw [Real.log_mul hH.ne' (prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j hj =>
      (hVpos i j hj).ne'),
    Real.log_prod (fun i _ => prod_ne_zero_iff.mpr fun j hj => (hVpos i j hj).ne'),
    Real.log_prod (fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne')] at hl
  simp only [Real.log_prod (fun j hj => (hVpos _ j hj).ne')] at hl
  have hIoi : ∀ i : Fin N, univ.filter (i < ·) = Ioi i := fun i => by ext; simp
  simp only [hIoi]
  linarith

/-- **(H), all ordered pairs.** `2 log H(ν) = ∑_{u, v} charge(u) charge(v) log G(1 + |u − v|)`. -/
theorem two_log_hookProd_eq (hν : Antitone ν) (hM : ∀ i, ν i ≤ M) :
    2 * Real.log (RMT.hookProd ν) = ∑ u ∈ window N M, ∑ v ∈ window N M,
      (charge ν u : ℝ) * charge ν v * kern (u - v) := by
  have inner : ∀ u, ∑ v ∈ window N M, (charge ν u : ℝ) * charge ν v * kern (u - v) =
      (charge ν u : ℝ) * (∑ j, (kern (u - (maya ν j + 1)) - kern (u - maya ν j)) +
        kern (u - -(N : ℤ))) := fun u => by
    rw [← sum_charge hν hM (fun v => kern (u - v)), mul_sum]
    exact sum_congr rfl fun v _ => by ring
  simp only [inner]
  rw [sum_charge hν hM (fun u => ∑ j, (kern (u - (maya ν j + 1)) - kern (u - maya ν j)) +
    kern (u - -(N : ℤ))), log_hookProd hν]
  have d2 : ∀ a b : ℤ, kern (a + 1 - (b + 1)) - kern (a + 1 - b) -
      (kern (a - (b + 1)) - kern (a - b)) = -Real.log |((a - b : ℤ) : ℝ)| := fun a b => by
    have := kern_second (a - b)
    rw [show a + 1 - (b + 1) = a - b by ring, show a + 1 - b = a - b + 1 by ring,
      show a - (b + 1) = a - b - 1 by ring]
    linarith
  have e1 : ∀ i : Fin N, kern (maya ν i + 1 - -(N : ℤ)) - kern (maya ν i - -(N : ℤ)) =
      Real.log ((maya ν i + N).toNat)! := fun i => by
    have := kern_succ_sub (maya ν i + N) (by have := maya_mem (M := M) hM i; simp [window] at this; omega)
    rw [show maya ν i + 1 - -(N : ℤ) = maya ν i + N + 1 by ring,
      show maya ν i - -(N : ℤ) = maya ν i + N by ring]
    exact this
  have e2 : ∀ j : Fin N, kern (-(N : ℤ) - (maya ν j + 1)) - kern (-(N : ℤ) - maya ν j) =
      Real.log ((maya ν j + N).toNat)! := fun j => by
    rw [show -(N : ℤ) - (maya ν j + 1) = -(maya ν j + 1 - -(N : ℤ)) by ring,
      show -(N : ℤ) - maya ν j = -(maya ν j - -(N : ℤ)) by ring, kern_neg, kern_neg]
    exact e1 j
  have hsplit : ∀ i : Fin N,
      (∑ j, (kern (maya ν i + 1 - (maya ν j + 1)) - kern (maya ν i + 1 - maya ν j)) +
          kern (maya ν i + 1 - -(N : ℤ))) -
        (∑ j, (kern (maya ν i - (maya ν j + 1)) - kern (maya ν i - maya ν j)) +
          kern (maya ν i - -(N : ℤ))) =
      -(∑ j, Real.log |((maya ν i - maya ν j : ℤ) : ℝ)|) + Real.log ((maya ν i + N).toNat)! := by
    intro i
    have ar : ∀ x y z w : ℝ, (x + z) - (y + w) = (x - y) + (z - w) := by intros; ring
    rw [← e1 i, ar, ← sum_sub_distrib, ← sum_neg_distrib]
    congr 1
    exact sum_congr rfl fun j _ => d2 _ _
  simp only [hsplit, sub_self, kern_zero, add_zero]
  rw [sum_congr rfl fun j _ => e2 j]
  have hsym := sum_sum_eq_two_mul (univ : Finset (Fin N))
    (fun i j => Real.log |((maya ν i - maya ν j : ℤ) : ℝ)|)
    (fun i j => by rw [← abs_neg]; push_cast; ring_nf) (fun i => by simp)
  have hpos : ∀ i : Fin N, ∑ j ∈ univ.filter (i < ·), Real.log |((maya ν i - maya ν j : ℤ) : ℝ)| =
      ∑ j ∈ univ.filter (i < ·), Real.log ((maya ν i - maya ν j : ℤ) : ℝ) := fun i =>
    sum_congr rfl fun j hj => by
      have := maya_strictAnti hν (mem_filter.mp hj).2
      rw [abs_of_pos (by exact_mod_cast (by omega : (0 : ℤ) < maya ν i - maya ν j))]
  rw [sum_add_distrib, sum_neg_distrib, hsym, sum_congr rfl fun i _ => hpos i]
  ring

/-- **(H)** `H(λ) = ∏_{corners u < v} G(1 + |u − v|)^{ε_u ε_v}`, in `ℚ` with integer exponents. -/
theorem hookProd_corners (hν : Antitone ν) (hM : ∀ i, ν i ≤ M) :
    (RMT.hookProd ν : ℚ) = ∏ u ∈ window N M, ∏ v ∈ (window N M).filter (u < ·),
      ((barnesG (1 + |u - v|).toNat : ℕ) : ℚ) ^ (charge ν u * charge ν v) := by
  have hpos : ∀ u v : ℤ, (0 : ℝ) < ((barnesG (1 + |u - v|).toNat : ℕ) : ℝ) := fun u v => by
    exact_mod_cast barnesG_pos _
  have hlog : Real.log (RMT.hookProd ν) = ∑ u ∈ window N M, ∑ v ∈ (window N M).filter (u < ·),
      (charge ν u : ℝ) * charge ν v * kern (u - v) := by
    have h := two_log_hookProd_eq hν hM
    rw [sum_sum_eq_two_mul _ _ (fun u v => by rw [← kern_neg, neg_sub]; ring)
      (fun u => by simp [kern_zero])] at h
    linarith
  have hH : (0 : ℝ) < RMT.hookProd ν := by
    have h := RMT.frobenius ν hν
    rcases Nat.eq_zero_or_pos (RMT.hookProd ν) with h0 | h0
    · rw [h0, zero_mul] at h
      exact absurd h.symm (prod_pos fun _ _ => Nat.factorial_pos _).ne'
    · exact_mod_cast h0
  have hR : (0 : ℝ) < ∏ u ∈ window N M, ∏ v ∈ (window N M).filter (u < ·),
      ((barnesG (1 + |u - v|).toNat : ℕ) : ℝ) ^ (charge ν u * charge ν v) :=
    prod_pos fun u _ => prod_pos fun v _ => zpow_pos (hpos u v) _
  have key : (RMT.hookProd ν : ℝ) = ∏ u ∈ window N M, ∏ v ∈ (window N M).filter (u < ·),
      ((barnesG (1 + |u - v|).toNat : ℕ) : ℝ) ^ (charge ν u * charge ν v) := by
    apply Real.log_injOn_pos hH hR
    rw [hlog, Real.log_prod (fun u _ => (prod_pos fun v _ => zpow_pos (hpos u v) _).ne')]
    refine sum_congr rfl fun u _ => ?_
    rw [Real.log_prod (fun v _ => (zpow_pos (hpos u v) _).ne')]
    refine sum_congr rfl fun v _ => ?_
    rw [Real.log_zpow, kern]
    push_cast; ring
  have : ((RMT.hookProd ν : ℚ) : ℝ) = ((∏ u ∈ window N M, ∏ v ∈ (window N M).filter (u < ·),
      ((barnesG (1 + |u - v|).toNat : ℕ) : ℚ) ^ (charge ν u * charge ν v) : ℚ) : ℝ) := by
    push_cast; exact key
  exact Rat.cast_injective this

end Hook

end RMT.Symmetric.Corners

end
