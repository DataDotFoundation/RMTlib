import RMTlib.Symmetric.Bialternant
set_option autoImplicit false

/-!
# Sums over sign choices: the symplectic and orthogonal denominators

Formalisation of the lemmas of `archives/lower_2/full_moments_2.tex` (Dehaye, *Combinatorics of the
lower order terms in the moment conjectures: the other families*, draft). In the CFKRS recipe for
the symplectic and orthogonal families (CFKRS (4.5.6), (4.5.11)–(4.5.12)), the unitary sum over
"swaps" becomes a sum over sign choices `ε ∈ {±1}^k` of the shifts, `α ↦ (ε_1 α_1, …, ε_k α_k)`,
against the Weyl denominators of type `D` (`∏_{i<j}`) and `C` (`∏_{i≤j}`). These lemmas evaluate
such sums on a Schur function. Write `δ = (k−1, …, 0)` (`stair`) and `s_l` for `schurV`.

* `sum_schurV_div_typeD` (the note's `full_choices`):
  `Σ_ε s_l(εx) / ∏_{i<j} (ε_i x_i + ε_j x_j) = 2^k s_ν(x²)` if every `l_j + δ_j` is even, else `0`.
* `sum_schurV_div_typeC` (`half_choices`):
  `Σ_ε s_l(εx) / ∏_{i≤j} (ε_i x_i + ε_j x_j) = s_ν(x²)` if every `l_j + δ_j` is odd, else `0`.
* `sum_sgn_schurV_div_typeD` (`half_choices2`):
  `Σ_ε (∏ ε_i) s_l(εx) / ∏_{i<j} (ε_i x_i + ε_j x_j) = 2^k (∏ x_i) s_ν(x²)` if every `l_j + δ_j` is
  odd, else `0`.

In each case `ν` is the partition with `ν + δ = ⌊(l + δ)/2⌋` (`halfShape`). The note states the
zero cases as "`Δ ⊄ l`" and "`Δ ∖ l` has an odd part"; here they are the single parity condition,
which forces the staircase (`stair_add_le`: `Δ(k−1) ⊆ l` in the even case, `Δ(k) ⊆ l` in the odd
one), so `ν` is a partition (`halfShape_antitone`).

## Proof

As in the note, with no division until the end. A determinant whose rows are each chosen from two
rows, summed over the choices, is the determinant of the row sums (`sum_det_choices`). Hence
`Σ_ε a_μ(εx) = det(x^μ + (−x)^μ)` and `Σ_ε (∏ ε_i) a_μ(εx) = det(x^μ − (−x)^μ)`, whose columns
vanish at the odd, resp. even, exponents (`sum_altV_signPt_eq`, `sum_sgn_altV_signPt_eq`, over any
commutative ring). The bialternant formula (`altV_add_stair_eq_mul_schurV`) and
`a_δ(εx) · ∏_{i<j} (ε_i x_i + ε_j x_j) = a_δ(x²)` (`altV_signPt_stair_mul`, from the Vandermonde
product `altV_pt_stair`) turn these into the Schur form.

## Hypotheses the note leaves implicit

* `a_δ(x²) ≠ 0`, i.e. the `x_i²` distinct, so that no denominator vanishes;
* for type `C`, `x_i ≠ 0` and `2 ≠ 0` (the diagonal factors `2 ε_i x_i`).

The note's proof of `half_choices` divides the alternant by `∏ ε_i x_i` and uses exponents
`l_j + δ_j − 1`, which is `−1` when `l_k = 0`. The proof here weights by `∏ ε_i` instead
(`half_choices2` first), which needs no such exponent.
-/

open Finset Matrix RMT.Symmetric

namespace RMT.Moments.OtherFamilies

variable {R : Type*} [CommRing R] {k : ℕ}

/-- **A determinant whose row `i` is chosen from two rows, summed over all choices, is the
determinant of the row sums** (multilinearity in the rows). -/
theorem sum_det_choices (u v : Matrix (Fin k) (Fin k) R) :
    ∑ ε : Fin k → Bool, det (of fun i j => if ε i then v i j else u i j) = det (u + v) := by
  simp only [det_apply, of_apply, Matrix.add_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  have hre : ∀ ε : Fin k → Bool, ∏ i, (if ε (σ i) then v (σ i) i else u (σ i) i) =
      ∏ m, (if ε m then v m (σ.symm m) else u m (σ.symm m)) := fun ε => by
    rw [← Equiv.prod_comp σ (fun m => if ε m then v m (σ.symm m) else u m (σ.symm m))]
    simp
  simp_rw [hre]
  rw [← Fintype.prod_sum (fun m (b : Bool) => if b then v m (σ.symm m) else u m (σ.symm m)),
    ← Equiv.prod_comp σ]
  simp [add_comm]

/-- `x ∈ R^k` as a point `ℕ → R`, padded by `0` (the form `altV` takes). -/
def pt (x : Fin k → R) : ℕ → R := fun i => if h : i < k then x ⟨i, h⟩ else 0

/-- The point `ε·x = (ε_0 x_0, …, ε_{k−1} x_{k−1})`, with `ε_i = −1` where `ε i = true`. -/
def signPt (x : Fin k → R) (ε : Fin k → Bool) : ℕ → R :=
  pt fun i => if ε i then -x i else x i

/-- The point `x² = (x_0², …, x_{k−1}²)`. -/
def sqPt (x : Fin k → R) : ℕ → R := pt fun i => x i ^ 2

/-- The sign `ε_i ∈ {±1}`. -/
def sgn (b : Bool) : R := if b then -1 else 1

theorem altV_pt (y : Fin k → R) (μ : Fin k → ℕ) :
    altV (pt y) k μ = det (of fun i j => y i ^ μ j) := by
  simp [altV, pt]

theorem altV_signPt (x : Fin k → R) (ε : Fin k → Bool) (μ : Fin k → ℕ) :
    altV (signPt x ε) k μ = det (of fun i j => if ε i then (-x i) ^ μ j else x i ^ μ j) := by
  rw [signPt, altV_pt]; congr 1; ext i j; simp only [of_apply]; split_ifs <;> rfl

/-- **The sum of the alternants over all sign choices** is the determinant of `x^μ + (−x)^μ`. -/
theorem sum_altV_signPt (x : Fin k → R) (μ : Fin k → ℕ) :
    ∑ ε, altV (signPt x ε) k μ = det (of fun i j => x i ^ μ j + (-x i) ^ μ j) := by
  simp_rw [altV_signPt]
  exact sum_det_choices (of fun i j => x i ^ μ j) (of fun i j => (-x i) ^ μ j)

/-- **The same sum weighted by `∏ ε_i`** is the determinant of `x^μ − (−x)^μ`. -/
theorem sum_sgn_altV_signPt (x : Fin k → R) (μ : Fin k → ℕ) :
    ∑ ε : Fin k → Bool, (∏ i, sgn (R := R) (ε i)) * altV (signPt x ε) k μ =
      det (of fun i j => x i ^ μ j - (-x i) ^ μ j) := by
  have h : ∀ ε : Fin k → Bool, (∏ i, sgn (R := R) (ε i)) * altV (signPt x ε) k μ =
      det (of fun i j => if ε i then -(-x i) ^ μ j else x i ^ μ j) := fun ε => by
    rw [altV_signPt, ← det_mul_column]
    congr 1; ext i j; simp only [of_apply, sgn]; split_ifs <;> ring
  simp_rw [h, sub_eq_add_neg]
  exact sum_det_choices (of fun i j => x i ^ μ j) (of fun i j => -(-x i) ^ μ j)

/-- **Type D (the note's `full_choices`, alternant form)**: summed over all sign choices, the
alternant `a_μ(εx)` vanishes unless every exponent is even, and then it is `2^k a_{μ/2}(x²)`. -/
theorem sum_altV_signPt_eq (x : Fin k → R) (μ : Fin k → ℕ) :
    ∑ ε, altV (signPt x ε) k μ =
      if ∀ j, Even (μ j) then 2 ^ k * altV (sqPt x) k (fun j => μ j / 2) else 0 := by
  rw [sum_altV_signPt]
  split_ifs with h
  · rw [sqPt, altV_pt]
    have e := det_smul (of fun i j => (x i ^ 2) ^ (μ j / 2)) (2 : R)
    rw [Fintype.card_fin] at e
    rw [← e]
    congr 1; ext i j
    obtain ⟨n, hn⟩ := h j
    simp only [of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hn, Even.neg_pow ⟨n, rfl⟩, show (n + n) / 2 = n by omega, ← pow_mul, two_mul]
    ring
  · simp only [not_forall] at h
    obtain ⟨j, hj⟩ := h
    exact det_eq_zero_of_column_eq_zero j fun i => by
      simp [Odd.neg_pow (Nat.not_even_iff_odd.mp hj)]

/-- **Type C (the note's `half_choices2`, alternant form)**: weighted by `∏ ε_i`, the sum vanishes
unless every exponent is odd, and then it is `2^k (∏ x_i) a_{(μ−1)/2}(x²)`. -/
theorem sum_sgn_altV_signPt_eq (x : Fin k → R) (μ : Fin k → ℕ) :
    ∑ ε : Fin k → Bool, (∏ i, sgn (R := R) (ε i)) * altV (signPt x ε) k μ =
      if ∀ j, Odd (μ j) then 2 ^ k * (∏ i, x i) * altV (sqPt x) k (fun j => μ j / 2) else 0 := by
  rw [sum_sgn_altV_signPt]
  split_ifs with h
  · rw [sqPt, altV_pt]
    have e := det_mul_column (fun i => 2 * x i) (of fun i j => (x i ^ 2) ^ (μ j / 2))
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at e
    rw [← e]
    congr 1; ext i j
    obtain ⟨n, hn⟩ := h j
    simp only [of_apply, hn, Odd.neg_pow ⟨n, rfl⟩, show (2 * n + 1) / 2 = n by omega, ← pow_mul]
    ring
  · simp only [not_forall] at h
    obtain ⟨j, hj⟩ := h
    exact det_eq_zero_of_column_eq_zero j fun i => by
      simp [Even.neg_pow (Nat.not_odd_iff_even.mp hj)]

/-- `∏_{i<j} f i j` swapped to the other order of summation. -/
theorem prod_Ioi_eq_prod_Iio {M : Type*} [CommMonoid M] (f : Fin k → Fin k → M) :
    ∏ i, ∏ j ∈ Ioi i, f i j = ∏ j, ∏ i ∈ Iio j, f i j := by
  rw [Finset.prod_sigma', Finset.prod_sigma']
  refine Finset.prod_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp

/-- **The staircase alternant is the Vandermonde product**: `a_δ(y) = ∏_{i<j} (y_i − y_j)`. -/
theorem altV_pt_stair (y : Fin k → R) :
    altV (pt y) k (stair k) = ∏ i, ∏ j ∈ Ioi i, (y i - y j) := by
  rw [altV_pt]
  have e : (of fun i j => y i ^ stair k j) =
      (vandermonde (y ∘ Fin.revPerm)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j; simp [vandermonde, stair, Fin.val_rev]; congr 1; omega
  rw [e, det_submatrix_equiv_self, det_vandermonde,
    ← Equiv.prod_comp Fin.revPerm, prod_Ioi_eq_prod_Iio]
  refine Finset.prod_congr rfl fun j _ => ?_
  refine Finset.prod_nbij' (fun i => Fin.revPerm i) (fun i => Fin.revPerm i) ?_ ?_ ?_ ?_ ?_ <;>
    simp [Fin.rev_lt_rev]
  intro a ha; rw [Fin.rev_lt_iff]; exact ha

/-! ### Exponents of constant parity -/

/-- If `l + δ` has entries of one parity and `l` is antitone, the halves of `l + δ` drop by at least
one at each step: `(l+δ)_j / 2 + (j − i) ≤ (l+δ)_i / 2` for `i ≤ j`. -/
theorem half_chain {l : Fin k → ℕ} (hl : Antitone l) (p : ℕ)
    (hp : ∀ j, (l j + stair k j) % 2 = p) {i j : Fin k} (hij : i ≤ j) :
    (l j + stair k j) / 2 + (j - i : ℕ) ≤ (l i + stair k i) / 2 := by
  obtain ⟨n, hn⟩ : ∃ n, (j : ℕ) = i + n := ⟨j - i, by omega⟩
  induction n generalizing j with
  | zero =>
    have : j = i := Fin.ext (by omega)
    subst this; simp
  | succ n ih =>
    have hlt : (i : ℕ) + n < k := by omega
    set j' : Fin k := ⟨i + n, hlt⟩
    have h1 := ih (j := j') (by simp [j', Fin.le_def]) rfl
    have hjj : j' ≤ j := by simp [j', Fin.le_def]; omega
    have hl' := hl hjj
    have p1 := hp j; have p2 := hp j'
    simp only [stair, j'] at h1 p1 p2 hl' ⊢
    omega

/-- **The parity condition forces the staircase**: if every `l_j + δ_j` has the parity `p`, then
`l_j ≥ δ_j + p` (`p = 0`: `Δ(k−1) ⊆ l`; `p = 1`: `Δ(k) ⊆ l`). -/
theorem stair_add_le {l : Fin k → ℕ} (hl : Antitone l) (p : ℕ)
    (hp : ∀ j, (l j + stair k j) % 2 = p) (j : Fin k) : stair k j + p ≤ l j := by
  have hk : k - 1 < k := by have := j.isLt; omega
  have h := half_chain hl p hp (i := j) (j := ⟨k - 1, hk⟩) (by simp [Fin.le_def]; omega)
  have p1 := hp j; have p2 := hp ⟨k - 1, hk⟩
  simp only [stair] at h p1 p2 ⊢
  omega

/-- The partition `ν` with `ν + δ = (l + δ)/2`. -/
def halfShape (l : Fin k → ℕ) : Fin k → ℕ := fun j => (l j + stair k j) / 2 - stair k j

theorem halfShape_add_stair {l : Fin k → ℕ} (hl : Antitone l) (p : ℕ)
    (hp : ∀ j, (l j + stair k j) % 2 = p) :
    halfShape l + stair k = fun j => (l j + stair k j) / 2 := by
  ext j
  have := stair_add_le hl p hp j
  simp only [Pi.add_apply, halfShape]
  omega

theorem halfShape_antitone {l : Fin k → ℕ} (hl : Antitone l) (p : ℕ)
    (hp : ∀ j, (l j + stair k j) % 2 = p) : Antitone (halfShape l) := by
  intro i j hij
  have h := half_chain hl p hp hij
  have h1 := stair_add_le hl p hp i
  have h2 := stair_add_le hl p hp j
  simp only [halfShape, stair] at h h1 h2 ⊢
  have : (i : ℕ) ≤ j := hij
  omega

/-! ### The Schur function form, over a field -/

section Field

variable {K : Type*} [Field K]

/-- The vector `ε·x`. -/
def signVec (x : Fin k → K) (ε : Fin k → Bool) : Fin k → K := fun i => if ε i then -x i else x i

theorem signPt_eq (x : Fin k → K) (ε : Fin k → Bool) : signPt x ε = pt (signVec x ε) := rfl

theorem signVec_sq (x : Fin k → K) (ε : Fin k → Bool) (i : Fin k) :
    signVec x ε i ^ 2 = x i ^ 2 := by
  unfold signVec; split_ifs <;> ring

/-- **The type-D denominator**: `a_δ(εx) · ∏_{i<j} (ε_i x_i + ε_j x_j) = a_δ(x²)`, since
`(ε_i x_i − ε_j x_j)(ε_i x_i + ε_j x_j) = x_i² − x_j²`. -/
theorem altV_signPt_stair_mul (x : Fin k → K) (ε : Fin k → Bool) :
    altV (signPt x ε) k (stair k) * ∏ i, ∏ j ∈ Ioi i, (signVec x ε i + signVec x ε j) =
      altV (sqPt x) k (stair k) := by
  rw [signPt_eq, altV_pt_stair, sqPt, altV_pt_stair, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [← signVec_sq x ε i, ← signVec_sq x ε j]; ring

/-- Each summand, as an alternant over the fixed denominator `a_δ(x²)`. -/
theorem schurV_signPt_div (x : Fin k → K) (hx : altV (sqPt x) k (stair k) ≠ 0)
    {l : Fin k → ℕ} (hl : Antitone l) (ε : Fin k → Bool) :
    schurV (signPt x ε) k k l / ∏ i, ∏ j ∈ Ioi i, (signVec x ε i + signVec x ε j) =
      altV (signPt x ε) k (l + stair k) / altV (sqPt x) k (stair k) := by
  have hd := altV_signPt_stair_mul x ε
  rw [← hd] at hx
  have hA := left_ne_zero_of_mul hx
  have hP := right_ne_zero_of_mul hx
  rw [altV_add_stair_eq_mul_schurV _ _ _ hl, ← hd]
  field_simp

/-- **The note's `full_choices` (type `D`)**: for a partition `l` of length `≤ k`,
`Σ_{ε ∈ {±1}^k} s_l(εx) / ∏_{i<j} (ε_i x_i + ε_j x_j)` is `2^k s_ν(x²)` when every `l_j + δ_j` is
even, with `ν + δ = (l + δ)/2` (then `Δ(k−1) ⊆ l`, `stair_add_le`), and `0` otherwise. -/
theorem sum_schurV_div_typeD (x : Fin k → K) (hx : altV (sqPt x) k (stair k) ≠ 0)
    {l : Fin k → ℕ} (hl : Antitone l) :
    ∑ ε, schurV (signPt x ε) k k l / ∏ i, ∏ j ∈ Ioi i, (signVec x ε i + signVec x ε j) =
      if ∀ j, Even (l j + stair k j) then 2 ^ k * schurV (sqPt x) k k (halfShape l) else 0 := by
  simp_rw [schurV_signPt_div x hx hl]
  rw [← sum_div, sum_altV_signPt_eq]
  simp only [Pi.add_apply]
  split_ifs with h
  · have hp : ∀ j, (l j + stair k j) % 2 = 0 := fun j => Nat.even_iff.mp (h j)
    rw [← halfShape_add_stair hl 0 hp,
      altV_add_stair_eq_mul_schurV _ _ _ (halfShape_antitone hl 0 hp)]
    field_simp
  · simp

/-- **The note's `half_choices2`**: weighted by `∏ ε_i`, the type-`D` sum is
`2^k (∏ x_i) s_ν(x²)` when every `l_j + δ_j` is odd (then `Δ(k) ⊆ l`), and `0` otherwise. -/
theorem sum_sgn_schurV_div_typeD (x : Fin k → K) (hx : altV (sqPt x) k (stair k) ≠ 0)
    {l : Fin k → ℕ} (hl : Antitone l) :
    ∑ ε : Fin k → Bool, (∏ i, sgn (R := K) (ε i)) *
        (schurV (signPt x ε) k k l / ∏ i, ∏ j ∈ Ioi i, (signVec x ε i + signVec x ε j)) =
      if ∀ j, Odd (l j + stair k j) then 2 ^ k * (∏ i, x i) * schurV (sqPt x) k k (halfShape l)
      else 0 := by
  simp_rw [schurV_signPt_div x hx hl, ← mul_div_assoc]
  rw [← sum_div, sum_sgn_altV_signPt_eq]
  simp only [Pi.add_apply]
  split_ifs with h
  · have hp : ∀ j, (l j + stair k j) % 2 = 1 := fun j => Nat.odd_iff.mp (h j)
    rw [← halfShape_add_stair hl 1 hp,
      altV_add_stair_eq_mul_schurV _ _ _ (halfShape_antitone hl 1 hp)]
    field_simp
  · simp

theorem prod_signVec (x : Fin k → K) (ε : Fin k → Bool) :
    ∏ i, signVec x ε i = (∏ i, sgn (R := K) (ε i)) * ∏ i, x i := by
  rw [← prod_mul_distrib]; refine prod_congr rfl fun i _ => ?_
  unfold signVec sgn; split_ifs <;> ring

theorem prod_sgn_mul_self (ε : Fin k → Bool) :
    (∏ i, sgn (R := K) (ε i)) * ∏ i, sgn (R := K) (ε i) = 1 := by
  rw [← prod_mul_distrib]; refine prod_eq_one fun i _ => ?_
  unfold sgn; split_ifs <;> ring

/-- `∏_{i ≤ j}` is `∏_{i<j}` times the diagonal `∏_i 2 z_i`. -/
theorem prod_Ici_add (z : Fin k → K) :
    ∏ i, ∏ j ∈ Ici i, (z i + z j) = (∏ i, ∏ j ∈ Ioi i, (z i + z j)) * ∏ i, (2 * z i) := by
  rw [← prod_mul_distrib]; refine prod_congr rfl fun i _ => ?_
  rw [← Finset.insert_Ioi, prod_insert (by simp)]; ring

/-- **The note's `half_choices` (type `C`)**: for a partition `l` of length `≤ k` and nonzero
`x_i`, `Σ_{ε ∈ {±1}^k} s_l(εx) / ∏_{i ≤ j} (ε_i x_i + ε_j x_j)` is `s_ν(x²)` when every `l_j + δ_j`
is odd, with `ν + δ = ⌊(l + δ)/2⌋` (then `Δ(k) ⊆ l`), and `0` otherwise. -/
theorem sum_schurV_div_typeC (x : Fin k → K) (hx : altV (sqPt x) k (stair k) ≠ 0)
    (hx0 : ∀ i, x i ≠ 0) (h2 : (2 : K) ≠ 0) {l : Fin k → ℕ} (hl : Antitone l) :
    ∑ ε, schurV (signPt x ε) k k l / ∏ i, ∏ j ∈ Ici i, (signVec x ε i + signVec x ε j) =
      if ∀ j, Odd (l j + stair k j) then schurV (sqPt x) k k (halfShape l) else 0 := by
  have hX : (∏ i, x i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hx0 i
  have h2k : (2 : K) ^ k ≠ 0 := pow_ne_zero k h2
  have hs : ∀ ε : Fin k → Bool,
      schurV (signPt x ε) k k l / ∏ i, ∏ j ∈ Ici i, (signVec x ε i + signVec x ε j) =
        (∏ i, sgn (R := K) (ε i)) *
          (schurV (signPt x ε) k k l / ∏ i, ∏ j ∈ Ioi i, (signVec x ε i + signVec x ε j)) /
          (2 ^ k * ∏ i, x i) := fun ε => by
    rw [prod_Ici_add, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_signVec]
    have := prod_sgn_mul_self (K := K) ε
    have hS : (∏ i, sgn (R := K) (ε i)) ≠ 0 := left_ne_zero_of_mul (by rw [this]; exact one_ne_zero)
    field_simp
    rw [sq, this, mul_one]
  simp_rw [hs]
  rw [← sum_div, sum_sgn_schurV_div_typeD x hx hl]
  split_ifs
  · field_simp
  · simp

end Field

end RMT.Moments.OtherFamilies
