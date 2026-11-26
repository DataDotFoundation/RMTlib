import RMTlib.Symmetric.JacobiTrudi
import MeaningLib.Frame.Pattern

/-!
# Specialising the Cauchy identity at a point

RMTlib's Cauchy identity is a weight-preserving bijection (RSK, `rskEquiv`) between `ℕ`-matrices
and pairs of semistandard tableaux of the same shape (`RMT.Symmetric.cauchy`,
`cauchy_prod_ssyt`). This file evaluates its weights at a point, as the design rule of the
programme prescribes (one formal identity, specialised place by place):

* in each degree `d` the two sides are finite sets, so evaluating the weights at values
  `α, β : ℕ → R` in any commutative ring gives a finite identity (`sum_antiParts_schurV`):
  `Σ_{|λ| = d} s_λ(α) s_λ(β) = Σ_{|F| = d} ∏ (α_j β_i)^{F(i, j)}`;
* collecting degrees with a variable `X` gives the formal identity in one variable
  `(Σ_d (Σ_{|λ| = d} s_λ(α) s_λ(β)) X^d) · ∏_{i,j} (1 − α_j β_i X) = 1` (`cauchy_powerSeries`);
* in `ℂ`, under absolute convergence of `Σ_λ |s_λ(α) s_λ(β)| |T|^{|λ|}`, the series is evaluated at
  `X = T`: `Σ_λ s_λ(α) s_λ(β) T^{|λ|} = ∏ (1 − α_j β_i T)⁻¹` (`cauchy_hasSum`). This is the only
  analytic step, and it is the evaluation of a power series against a polynomial.

With `N = m = n = 2` and the two-row formula `s_{(p+j, j)}(x, y) = (x y)^j h_p(x, y)`
(`schurV_two_two`), the one-row part of the kernel gives the local `GL₂ × GL₂` generating series
`(Σ_k c^k h_k(x, y) h_k(x', y') X^k) · ∏ (1 − a b c X) = 1 − x y x' y' c² X²`
(`oneRow_cauchy_two`).

The Schur polynomials are evaluated tableau sums (`schurV`), equal to Jacobi–Trudi determinants
(`schurV_eq_det`). The bridge (`RMTlibBridge.RankinSelberg`) identifies them with the RH
formalisation's `GlobalTheory.JSW.schurAt` and derives its finite-place Rankin–Selberg Euler
product from `cauchy_hasSum`.

## Main results

* `sum_antiParts_schurV`: the Cauchy identity in degree `d`, evaluated.
* `cauchy_powerSeries`: the Cauchy identity in one variable over any commutative ring.
* `hasSum_of_mk_mul_prod_eq_one`: evaluating `(Σ c_d X^d) · ∏ (1 − γ_p X) = 1` at a point.
* `cauchy_hasSum`: the Cauchy identity in `ℂ`.
* `schurV_two_two`: two-row Schur polynomials in two variables.
* `oneRow_cauchy_two`: the local `GL₂ × GL₂` generating series.
* `oneRow_cauchy_two_of`: the same, from any proof of the Cauchy identity in two variables.
-/

open Finset

namespace RMT.Symmetric

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthSuper (HStrip size rowSum rectSum)
open RMT.RSK.GrowthBij (IsHChain Fb bos)
open RMT.RSK.GrowthGeneric (grow)

variable {N n m : ℕ}

/-! ## Degree by degree: evaluating the RSK bijection -/

open Classical in
/-- The antitone vectors `l : Fin N → ℕ` of size `d` (partitions of `d` with at most `N` parts). -/
noncomputable def antiParts (N d : ℕ) : Finset (Fin N → ℕ) :=
  (Finset.Nat.antidiagonalTuple N d).filter Antitone

/-- Membership in `antiParts`. -/
theorem mem_antiParts {d : ℕ} {l : Fin N → ℕ} : l ∈ antiParts N d ↔ ∑ i, l i = d ∧ Antitone l := by
  classical
  simp [antiParts, Finset.Nat.mem_antidiagonalTuple]

/-- `rectSum` is the sum of the entries of the rectangle. -/
theorem rectSum_eq (σ : ℕ → ℕ → ℕ) (j : ℕ) :
    ∀ i, rectSum σ i j = ∑ i' ∈ range i, ∑ j' ∈ range j, σ i' j'
  | 0 => rfl
  | i + 1 => by rw [Finset.sum_range_succ, ← rectSum_eq σ j i, ← rowSum_eq]; rfl

/-- The shape of the RSK image of `A` has size `Σ A`. -/
theorem size_shape_rskFwd (hm : m ≤ N) (A : Fin n → Fin m → ℕ) :
    size (rskFwd (N := N) A).1.1.shape = ∑ i, ∑ j, A i j := by
  show size (freeze m (fun j => grow Fb (zeros N) (extM A) n j) m) = _
  simp only [freeze, Nat.min_self]
  rw [RMT.RSK.GrowthSuper.size_grow_of_room bos bos (extM A) N
    (RMT.RSK.GrowthBij.admissible_bos _) n m (RMT.RSK.GrowthBij.room_bos _ N n m hm) n m le_rfl
    le_rfl, rectSum_eq, Finset.sum_range (fun i => ∑ j ∈ range m, extM A i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range (fun j => extM A i j)]
  simp [extM]

/-- The entries of a partition of length `N`, as a vector. -/
def vecOf (L : Part) : Fin N → ℕ := fun i => L.getD i 0

/-- The entries of a partition decrease. -/
theorem antitone_vecOf {L : Part} (h : RMT.RSK.GrowthSuper.Partition L) :
    Antitone (vecOf (N := N) L) := by
  have key : ∀ d k, L.getD (k + d) 0 ≤ L.getD k 0 := by
    intro d
    induction d with
    | zero => intro k; exact le_rfl
    | succ d ih => intro k; exact le_trans (partition_getD_succ h (k + d)) (ih k)
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  have := key (j - i) i
  simp only [vecOf]
  rwa [show (i : ℕ) + (j - i) = j by omega] at this

/-- Pairs of tableaux of shape `l`, the first with entries `< m`, the second `< n`. -/
abbrev PairV (N n m : ℕ) (l : Fin N → ℕ) : Type :=
  {pq : Tab N m × Tab N n // pq.1.shape = List.ofFn l ∧ pq.2.shape = List.ofFn l}

/-- Finitely many pairs of each shape. -/
instance (l : Fin N → ℕ) : Finite (PairV N n m l) :=
  Finite.of_injective (fun pq : PairV N n m l =>
    ((⟨pq.1.1, pq.2.1⟩ : TabV N m l), (⟨pq.1.2, pq.2.2⟩ : TabV N n l)))
    (fun _ _ h => by
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext (congrArg Subtype.val h.1) (congrArg Subtype.val h.2)))

/-- The pairs of each shape, as a `Fintype`. -/
noncomputable instance (l : Fin N → ℕ) : Fintype (PairV N n m l) := Fintype.ofFinite _

/-- `s_l(α) s_l(β)` as a sum over pairs of tableaux of shape `l`. -/
theorem schurV_mul_schurV {R : Type*} [CommRing R] (α β : ℕ → R) (l : Fin N → ℕ) :
    schurV α N m l * schurV β N n l
      = ∑ pq : PairV N n m l, evalMono α (pq.1.1.wt id) * evalMono β (pq.1.2.wt id) := by
  rw [schurV, schurV, Fintype.sum_mul_sum, ← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv Equiv.subtypeProdEquivProd _ _ fun _ => rfl).symm

/-- RSK preserves weights, evaluated: `x^P y^Q ↦ ∏ (α_j β_i)^{A i j}`. -/
theorem evalMono_rsk {R : Type*} [CommRing R] (α β : ℕ → R) (hm : m ≤ N) (A : Fin n → Fin m → ℕ) :
    evalMono α ((rskEquiv (N := N) hm A).1.1.wt id) * evalMono β ((rskEquiv (N := N) hm A).1.2.wt id)
      = ∏ i : Fin n, ∏ j : Fin m, (α j * β i) ^ A i j := by
  show evalMono α ((rskFwd (N := N) A).1.1.wt id) * evalMono β ((rskFwd (N := N) A).1.2.wt id) = _
  rw [wt_fst id hm, wt_snd id hm]
  simp only [evalMono_sum, evalMono_smul_single, id, ← Finset.prod_mul_distrib, mul_pow]

/-- **The Cauchy identity in degree `d`, evaluated**: for any commutative ring and any values
`α β : ℕ → R`, `Σ_{|λ| = d} s_λ(α₀, …, α_{m−1}) s_λ(β₀, …, β_{n−1})` is the sum over `ℕ`-matrices
`F` of total `d` of `∏ (α_j β_i) ^ F(i, j)`. The two finite sets are matched by RSK
(`rskEquiv`), which preserves weights. -/
theorem sum_antiParts_schurV {R : Type*} [CommRing R] (α β : ℕ → R) (hm : m ≤ N) (d : ℕ) :
    ∑ l ∈ antiParts N d, schurV α N m l * schurV β N n l
      = ∑ F ∈ (univ : Finset (Fin n × Fin m)).finsuppAntidiag d,
          ∏ p, (α p.2 * β p.1) ^ F p := by
  classical
  simp only [schurV_mul_schurV]
  rw [Finset.sum_sigma']
  let toPairs : (Σ l : Fin N → ℕ, PairV N n m l) → Pairs N n m :=
    fun x => ⟨x.2.1, x.2.2.1.trans x.2.2.2.symm⟩
  let toF : (Fin n → Fin m → ℕ) → (Fin n × Fin m →₀ ℕ) :=
    fun A => Finsupp.equivFunOnFinite.symm fun p => A p.1 p.2
  let ofF : (Fin n × Fin m →₀ ℕ) → (Fin n → Fin m → ℕ) := fun F i j => F (i, j)
  have hofto : ∀ A, ofF (toF A) = A := fun A => by funext i j; simp [ofF, toF]
  have htoof : ∀ F, toF (ofF F) = F := fun F => by ext p; simp [ofF, toF]
  have hsumF : ∀ F : Fin n × Fin m →₀ ℕ, ∑ p ∈ univ, F p = ∑ i, ∑ j, ofF F i j := fun F => by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hshape : ∀ A : Fin n → Fin m → ℕ, (rskEquiv (N := N) hm A).1.1.shape.length = N := fun A =>
    chain_length (rskEquiv (N := N) hm A).1.1.2.1 m le_rfl
  have hpart : ∀ A : Fin n → Fin m → ℕ, RMT.RSK.GrowthSuper.Partition (rskEquiv (N := N) hm A).1.1.shape := fun A =>
    chain_partition (rskEquiv (N := N) hm A).1.1.2.1 m le_rfl
  let ofPairs : Pairs N n m → (Σ l : Fin N → ℕ, PairV N n m l) := fun pq =>
    ⟨vecOf pq.1.1.shape, ⟨pq.1, (ofFn_getD (chain_length pq.1.1.2.1 m le_rfl)).symm,
      pq.2 ▸ (ofFn_getD (chain_length pq.1.1.2.1 m le_rfl)).symm⟩⟩
  refine Finset.sum_bij' (fun x _ => toF ((rskEquiv hm).symm (toPairs x)))
    (fun F _ => ofPairs (rskEquiv hm (ofF F))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨l, pq⟩ hx
    simp only [Finset.mem_sigma, mem_antiParts, Finset.mem_univ, and_true] at hx
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, fun _ _ => Finset.mem_univ _⟩
    rw [hsumF, hofto, ← size_shape_rskFwd (N := N) hm]
    have : rskFwd (N := N) ((rskEquiv hm).symm (toPairs ⟨l, pq⟩)) = toPairs ⟨l, pq⟩ :=
      (rskEquiv hm).apply_symm_apply _
    rw [this]
    show size pq.1.1.shape = d
    rw [pq.2.1, size, List.sum_ofFn, hx.1]
  · intro F hF
    rw [Finset.mem_finsuppAntidiag] at hF
    simp only [Finset.mem_sigma, mem_antiParts, Finset.mem_univ, and_true]
    refine ⟨?_, antitone_vecOf (hpart _)⟩
    have h1 : size (rskEquiv (N := N) hm (ofF F)).1.1.shape = ∑ i, ∑ j, ofF F i j :=
      size_shape_rskFwd (N := N) hm (ofF F)
    rw [← ofFn_getD (hshape (ofF F)), size, List.sum_ofFn] at h1
    show ∑ i, vecOf (rskEquiv (N := N) hm (ofF F)).1.1.shape i = d
    rw [← hF.1, hsumF]
    exact h1
  · rintro ⟨l, pq⟩ hx
    simp only [Finset.mem_sigma, mem_antiParts, Finset.mem_univ, and_true] at hx
    simp only [hofto, Equiv.apply_symm_apply]
    refine Sigma.subtype_ext ?_ rfl
    show vecOf pq.1.1.shape = l
    rw [pq.2.1]
    funext i
    simp [vecOf]
  · intro F _
    simp only [ofPairs, toPairs]
    rw [show (⟨(rskEquiv hm (ofF F)).1, _⟩ : Pairs N n m) = rskEquiv hm (ofF F) from rfl,
      Equiv.symm_apply_apply, htoof]
  · rintro ⟨l, pq⟩ _
    have := evalMono_rsk α β hm ((rskEquiv hm).symm (toPairs ⟨l, pq⟩))
    rw [Equiv.apply_symm_apply] at this
    rw [show (∏ p : Fin n × Fin m, (α p.2 * β p.1) ^ (toF ((rskEquiv hm).symm (toPairs ⟨l, pq⟩))) p)
      = ∏ i : Fin n, ∏ j : Fin m, (α j * β i) ^ ((rskEquiv hm).symm (toPairs ⟨l, pq⟩)) i j from by
        rw [Fintype.prod_prod_type]; simp [toF]]
    exact this

/-! ## The formal identity in one variable -/

section Formal

open PowerSeries

/-- The geometric series: `(Σ γ^k X^k) (1 − γ X) = 1`. -/
theorem mk_pow_mul_one_sub {R : Type*} [CommRing R] (γ : R) :
    PowerSeries.mk (fun k => γ ^ k) * (1 - C γ * X) = 1 := by
  ext k
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm (PowerSeries.mk _) (C γ), mul_assoc]
  rcases k with _ | k
  · simp
  · rw [coeff_C_mul, coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_one, pow_succ]
    simp [mul_comm]

/-- **The Cauchy identity in one variable `X`** (`X` counts boxes), over any commutative ring:

  `(Σ_d (Σ_{|λ| = d} s_λ(α₀, …, α_{m−1}) s_λ(β₀, …, β_{n−1})) X^d) · ∏_{i<n, j<m} (1 − α_j β_i X) = 1`

in `R⟦X⟧`. This is the specialisation of the formal Cauchy identity at `x_j ↦ α_j`,
`y_i ↦ β_i X`, computed degree by degree on the RSK bijection (`sum_antiParts_schurV`). -/
@[frame_pattern]
theorem cauchy_powerSeries {R : Type*} [CommRing R] (α β : ℕ → R) (hm : m ≤ N) :
    mk (fun d => ∑ l ∈ antiParts N d, schurV α N m l * schurV β N n l)
      * ∏ i : Fin n, ∏ j : Fin m, (1 - C (α j * β i) * X) = 1 := by
  classical
  have hmk : mk (fun d => ∑ l ∈ antiParts N d, schurV α N m l * schurV β N n l)
      = ∏ p : Fin n × Fin m, mk (fun k => (α p.2 * β p.1) ^ k) := by
    ext d
    rw [coeff_mk, sum_antiParts_schurV α β hm d, coeff_prod]
    simp [coeff_mk]
  rw [hmk, ← Fintype.prod_prod_type' (fun (i : Fin n) (j : Fin m) => (1 - C (α j * β i) * X : R⟦X⟧)),
    ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun p _ => mk_pow_mul_one_sub _

end Formal

/-! ## Evaluation in `ℂ` -/

section Complex

open PowerSeries in
/-- Evaluating a formal identity `(Σ c_d X^d) · ∏_p (1 − γ_p X) = 1` at a point `T` where
`Σ c_d T^d` converges absolutely. -/
theorem hasSum_of_mk_mul_prod_eq_one {ι : Type*} [Fintype ι] (c : ℕ → ℂ) (γ : ι → ℂ)
    (h : mk c * ∏ p, (1 - C (γ p) * X) = 1) (T : ℂ) (hs : Summable fun d => ‖c d * T ^ d‖) :
    (∏ p, (1 - γ p * T)) ≠ 0 ∧ HasSum (fun d => c d * T ^ d) (∏ p, (1 - γ p * T))⁻¹ := by
  set P : Polynomial ℂ := ∏ p, (1 - Polynomial.C (γ p) * Polynomial.X) with hP
  have hPc : ((P : Polynomial ℂ) : ℂ⟦X⟧) = ∏ p, (1 - C (γ p) * X) := by
    rw [hP, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp
  have hPe : P.eval T = ∏ p, (1 - γ p * T) := by
    simp [hP, Polynomial.eval_prod]
  set g : ℕ → ℂ := fun k => P.coeff k * T ^ k with hg
  have hgz : ∀ k ∉ range (P.natDegree + 1), g k = 0 := fun k hk => by
    simp only [Finset.mem_range, not_lt] at hk
    simp [hg, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k)]
  have hgs : Summable fun k => ‖g k‖ :=
    summable_of_ne_finset_zero (s := range (P.natDegree + 1)) fun k hk => by simp [hgz k hk]
  have htg : ∑' k, g k = P.eval T := by
    rw [tsum_eq_sum hgz, Polynomial.eval_eq_sum_range]
  have hmul : (∑' d, c d * T ^ d) * P.eval T = 1 := by
    rw [← htg, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hgs]
    have : ∀ n, ∑ kl ∈ antidiagonal n, c kl.1 * T ^ kl.1 * g kl.2
        = T ^ n * coeff n (mk c * (P : ℂ⟦X⟧)) := fun n => by
      rw [coeff_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun kl hkl => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
      simp only [hg, coeff_mk, Polynomial.coeff_coe, ← hkl, pow_add]
      ring
    simp only [this, hPc, h, coeff_one]
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp
  rw [hPe] at hmul
  refine ⟨right_ne_zero_of_mul_eq_one hmul, ?_⟩
  rw [← eq_inv_of_mul_eq_one_left hmul]
  exact hs.of_norm.hasSum

/-- **The Cauchy identity, specialised in `ℂ`**: if
`Σ_λ |s_λ(α) s_λ(β)| |T|^{|λ|}` converges (sum over antitone `λ : Fin N → ℕ`), then

  `Σ_λ s_λ(α₀, …, α_{m−1}) s_λ(β₀, …, β_{n−1}) T^{|λ|} = ∏_{i<n, j<m} (1 − α_j β_i T)⁻¹`,

and no factor vanishes. Here `s_λ` is the total weight of the semistandard tableaux of shape `λ`
(`schurV`), equal to the Jacobi–Trudi determinant (`schurV_eq_det`). The formal identity is
specialised degree by degree (`cauchy_powerSeries`); the only analysis is the evaluation of a
power series at `T`. -/
@[frame_pattern]
theorem cauchy_hasSum (α β : ℕ → ℂ) (hm : m ≤ N) (T : ℂ)
    (hs : Summable fun l : {l : Fin N → ℕ // Antitone l} =>
      ‖schurV α N m l.1 * schurV β N n l.1‖ * ‖T‖ ^ (∑ i, l.1 i)) :
    (∀ i : Fin n, ∀ j : Fin m, 1 - α j * β i * T ≠ 0) ∧
    HasSum (fun l : {l : Fin N → ℕ // Antitone l} =>
        schurV α N m l.1 * schurV β N n l.1 * T ^ (∑ i, l.1 i))
      (∏ i : Fin n, ∏ j : Fin m, (1 - α j * β i * T)⁻¹) := by
  classical
  set f : {l : Fin N → ℕ // Antitone l} → ℂ :=
    fun l => schurV α N m l.1 * schurV β N n l.1 * T ^ (∑ i, l.1 i) with hf
  have hfn : Summable fun l => ‖f l‖ := hs.congr fun l => by simp [hf, norm_pow]
  let e : (Σ d : ℕ, {l : Fin N → ℕ // l ∈ antiParts N d}) ≃ {l : Fin N → ℕ // Antitone l} :=
    { toFun := fun x => ⟨x.2.1, (mem_antiParts.mp x.2.2).2⟩
      invFun := fun l => ⟨∑ i, l.1 i, ⟨l.1, mem_antiParts.mpr ⟨rfl, l.2⟩⟩⟩
      left_inv := fun x => Sigma.subtype_ext (mem_antiParts.mp x.2.2).1 rfl
      right_inv := fun _ => rfl }
  set c : ℕ → ℂ := fun d => ∑ l ∈ antiParts N d, schurV α N m l * schurV β N n l with hc
  have hfib : ∀ d, ∑ x : {l : Fin N → ℕ // l ∈ antiParts N d}, f (e ⟨d, x⟩) = c d * T ^ d := by
    intro d
    rw [hc, Finset.sum_mul, ← Finset.sum_coe_sort (antiParts N d)]
    refine Fintype.sum_congr _ _ fun x => ?_
    simp only [hf, e, Equiv.coe_fn_mk, (mem_antiParts.mp x.2).1]
  have h1 : HasSum (fun d => c d * T ^ d) (∑' l, f l) := by
    have := ((e.hasSum_iff).mpr hfn.of_norm.hasSum).sigma (fun d => hasSum_fintype _)
    simpa only [Function.comp_apply, hfib] using this
  have h2 : Summable fun d => ‖c d * T ^ d‖ := by
    have := ((e.hasSum_iff).mpr hfn.hasSum).sigma (fun d => hasSum_fintype _)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ?_) this.summable
    rw [← hfib]
    exact norm_sum_le _ _
  have hγ := cauchy_powerSeries (R := ℂ) α β hm (n := n)
  rw [← Fintype.prod_prod_type' (fun (i : Fin n) (j : Fin m) =>
    (1 - PowerSeries.C (α j * β i) * PowerSeries.X))] at hγ
  obtain ⟨hne, hS⟩ := hasSum_of_mk_mul_prod_eq_one c (fun p : Fin n × Fin m => α p.2 * β p.1) hγ T h2
  rw [Fintype.prod_prod_type] at hne
  refine ⟨fun i j => ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ _)) j
      (Finset.mem_univ _)
  · have : ∑' l, f l = ∏ i : Fin n, ∏ j : Fin m, (1 - α j * β i * T)⁻¹ := by
      rw [h1.unique hS, Fintype.prod_prod_type, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => (Finset.prod_inv_distrib _).symm
    rw [← this]
    exact hfn.of_norm.hasSum

end Complex

/-! ## Two variables: the local `GL₂ × GL₂` series -/

section GL2

variable {R : Type*} [CommRing R]

/-- A pair is antitone iff `l₁ ≤ l₀`. -/
theorem antitone_fin_two {l : Fin 2 → ℕ} : Antitone l ↔ l 1 ≤ l 0 := by
  refine ⟨fun h => h (show (0 : Fin 2) ≤ 1 by decide), fun h i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> simp_all

/-- One variable: `s_μ(a₀) = a₀ ^ μ₀` if `μ₁ = 0`, else `0`. -/
theorem schurV_two_one (a : ℕ → R) (mu : Fin 2 → ℕ) :
    schurV a 2 1 mu = if mu 1 = 0 then a 0 ^ (mu 0) else 0 := by
  classical
  rw [schurV_succ]
  simp only [schurV_zero, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  have : (0 : Fin 2 → ℕ) ∈ interl mu ↔ mu 1 = 0 := by
    rw [mem_interl]
    constructor
    · intro h; have := h.1 0 1 rfl; simpa using this
    · intro h
      refine ⟨fun l j hj => ?_, fun t => Nat.zero_le _⟩
      fin_cases l <;> fin_cases j <;> simp_all
  by_cases h : mu 1 = 0
  · rw [ite_eq_left (this.mpr h), ite_eq_left h, Fin.sum_univ_two, h]
    simp
  · rw [ite_eq_right (fun h' => h (this.mp h')), ite_eq_right h]

/-- **Two-row Schur polynomials in two variables**:
`s_{(p+j, j)}(x, y) = (x y)^j h_p(x, y)`, with `h_p(x, y) = Σ_{i ≤ p} x^i y^{p−i}`. -/
theorem schurV_two_two (a : ℕ → R) (p j : ℕ) :
    schurV a 2 2 ![p + j, j]
      = (a 0 * a 1) ^ j * ∑ i ∈ range (p + 1), a 0 ^ i * a 1 ^ (p - i) := by
  classical
  rw [schurV_succ]
  simp only [schurV_two_one, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  rw [Finset.mul_sum]
  have hmem : ∀ mu, mu ∈ (interl ![p + j, j]).filter (fun mu => mu 1 = 0) ↔
      mu 1 = 0 ∧ j ≤ mu 0 ∧ mu 0 ≤ p + j := by
    intro mu
    simp only [Finset.mem_filter, mem_interl]
    constructor
    · rintro ⟨⟨h1, h2⟩, h0⟩
      have hb := h1 0 1 rfl
      have ht := h2 0
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hb ht
      exact ⟨h0, hb, ht⟩
    · rintro ⟨h0, hb, ht⟩
      refine ⟨⟨fun l j' hj => ?_, fun t => ?_⟩, h0⟩
      · fin_cases l <;> fin_cases j' <;> simp_all
      · fin_cases t <;> simp_all
  refine Finset.sum_nbij' (fun mu => mu 0 - j) (fun i => ![i + j, 0]) ?_ ?_ ?_ ?_ ?_
  · intro mu hmu
    have := (hmem mu).mp hmu
    simp only [Finset.mem_range]; omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [hmem]; simp; omega
  · intro mu hmu
    have := (hmem mu).mp hmu
    funext t; fin_cases t <;> simp [this.1]; omega
  · intro i _; simp
  · intro mu hmu
    have := (hmem mu).mp hmu
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, this.1, add_zero]
    obtain ⟨k, hk⟩ : ∃ k, mu 0 = j + k := ⟨mu 0 - j, by omega⟩
    rw [hk, show p + j + j - (j + k) = j + (p - k) by omega, show j + k - j = k by omega]
    ring

/-- `schurV_two_two` for an arbitrary antitone pair. -/
theorem schurV_two_two' (a : ℕ → R) (l : Fin 2 → ℕ) (hl : l 1 ≤ l 0) :
    schurV a 2 2 l
      = (a 0 * a 1) ^ l 1 * ∑ i ∈ range (l 0 - l 1 + 1), a 0 ^ i * a 1 ^ (l 0 - l 1 - i) := by
  rw [← schurV_two_two]
  congr 1
  funext t; fin_cases t <;> simp; omega

open PowerSeries

/-- `Σ_{k} e^k X^{2k}` inverts `1 − e X²`. -/
theorem mk_even_mul_one_sub (e : R) :
    PowerSeries.mk (fun k => if Even k then e ^ (k / 2) else 0) * (1 - C e * X ^ 2) = 1 := by
  ext k
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm (PowerSeries.mk _) (C e), mul_assoc,
    coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one]
  rcases k with _ | _ | k
  · simp
  · simp
  · have h2 : 2 ≤ k + 2 := by omega
    have hev : Even (k + 2) ↔ Even k := by simp [Nat.even_add]
    simp only [ite_eq_left h2, coeff_mk, show k + 2 - 2 = k by omega,
      ite_eq_right (show k + 2 ≠ 0 by omega)]
    by_cases hk : Even k
    · rw [ite_eq_left (hev.mpr hk), ite_eq_left hk, show (k + 2) / 2 = k / 2 + 1 by omega, pow_succ]
      ring
    · rw [ite_eq_right (fun h => hk (hev.mp h)), ite_eq_right hk]
      ring

/-- **The local `GL₂ × GL₂` generating series from any proof of the Cauchy identity in two
variables**: `oneRow_cauchy_two`, with the Cauchy identity `cauchy_powerSeries` (`N = m = n = 2`)
as a hypothesis `hC`. The rest of the argument is the two-row formula `schurV_two_two`. This is
the form in which the series is derived through the local interface
(`RMT.Places.oneRow_cauchy_two_at`). -/
theorem oneRow_cauchy_two_of
    (hC : ∀ α β : ℕ → R, PowerSeries.mk (fun d => ∑ l ∈ antiParts 2 d, schurV α 2 2 l * schurV β 2 2 l)
      * ∏ i : Fin 2, ∏ j : Fin 2, (1 - C (α j * β i) * X) = 1)
    (x y x' y' c : R) :
    PowerSeries.mk (fun k => c ^ k * (∑ i ∈ range (k + 1), x ^ i * y ^ (k - i))
        * (∑ i ∈ range (k + 1), x' ^ i * y' ^ (k - i)))
      * ((1 - C (x * x' * c) * X) * (1 - C (x * y' * c) * X)
        * (1 - C (y * x' * c) * X) * (1 - C (y * y' * c) * X))
      = 1 - C (x * y * x' * y' * c ^ 2) * X ^ 2 := by
  classical
  set a : ℕ → R := fun i => if i = 0 then x else y with ha
  set b : ℕ → R := fun i => if i = 0 then c * x' else c * y' with hb
  set e : R := x * y * x' * y' * c ^ 2 with he
  set g : ℕ → R := fun k => c ^ k * (∑ i ∈ range (k + 1), x ^ i * y ^ (k - i))
    * (∑ i ∈ range (k + 1), x' ^ i * y' ^ (k - i)) with hg
  set E : R⟦X⟧ := PowerSeries.mk (fun k => if Even k then e ^ (k / 2) else 0) with hE
  have hC := hC a b
  have hhb : ∀ k, ∑ i ∈ range (k + 1), b 0 ^ i * b 1 ^ (k - i)
      = c ^ k * ∑ i ∈ range (k + 1), x' ^ i * y' ^ (k - i) := fun k => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    simp only [hb, ite_eq_left, mul_pow, one_ne_zero, ite_false]
    rw [show c ^ k = c ^ i * c ^ (k - i) by rw [← pow_add]; congr 1; omega]
    ring
  have hterm : ∀ l : Fin 2 → ℕ, l 1 ≤ l 0 →
      schurV a 2 2 l * schurV b 2 2 l = e ^ l 1 * g (l 0 - l 1) := by
    intro l hl
    rw [schurV_two_two' a l hl, schurV_two_two' b l hl, hhb]
    simp only [ha, hb, he, hg, ite_eq_left, one_ne_zero, ite_false]
    ring
  have hCgE : PowerSeries.mk (fun d => ∑ l ∈ antiParts 2 d, schurV a 2 2 l * schurV b 2 2 l)
      = PowerSeries.mk g * E := by
    ext d
    rw [coeff_mk, coeff_mul]
    simp only [hE, coeff_mk, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hmem : ∀ l : Fin 2 → ℕ, l ∈ antiParts 2 d ↔ l 0 + l 1 = d ∧ l 1 ≤ l 0 := fun l => by
      rw [mem_antiParts, Fin.sum_univ_two, antitone_fin_two]
    refine Finset.sum_nbij' (fun l => (l 0 - l 1, 2 * l 1)) (fun x => ![x.1 + x.2 / 2, x.2 / 2])
      ?_ ?_ ?_ ?_ ?_
    · intro l hl
      have := (hmem l).mp hl
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
      exact ⟨by omega, even_two_mul _⟩
    · rintro ⟨u, w⟩ huw
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at huw
      obtain ⟨huw, ⟨r, rfl⟩⟩ := huw
      rw [hmem]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · intro l hl
      have := (hmem l).mp hl
      funext t; fin_cases t
      · simp; omega
      · simp
    · rintro ⟨u, w⟩ huw
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at huw
      obtain ⟨huw, ⟨r, rfl⟩⟩ := huw
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.injEq]
      omega
    · intro l hl
      have := (hmem l).mp hl
      rw [hterm l this.2, show 2 * l 1 / 2 = l 1 by omega, mul_comm]
  have hprod : ∏ i : Fin 2, ∏ j : Fin 2, (1 - C (a j * b i) * X)
      = (1 - C (x * x' * c) * X) * (1 - C (x * y' * c) * X)
        * (1 - C (y * x' * c) * X) * (1 - C (y * y' * c) * X) := by
    simp only [Fin.prod_univ_two, ha, hb, Fin.val_zero, Fin.val_one, ite_eq_left, one_ne_zero,
      ite_false, show x * (c * x') = x * x' * c by ring, show y * (c * x') = y * x' * c by ring,
      show x * (c * y') = x * y' * c by ring, show y * (c * y') = y * y' * c by ring]
    ring
  rw [hCgE, hprod] at hC
  have h1 : E * (1 - C e * X ^ 2) = 1 := by rw [hE]; exact mk_even_mul_one_sub e
  set Q := (1 - C (x * x' * c) * X) * (1 - C (x * y' * c) * X)
        * (1 - C (y * x' * c) * X) * (1 - C (y * y' * c) * X)
  calc PowerSeries.mk g * Q = PowerSeries.mk g * Q * (E * (1 - C e * X ^ 2)) := by
        rw [h1, mul_one]
    _ = (PowerSeries.mk g * E * Q) * (1 - C e * X ^ 2) := by ring
    _ = 1 - C e * X ^ 2 := by rw [hC, one_mul]

/-- **The local `GL₂ × GL₂` generating series from the Cauchy identity**: with
`h_k(x, y) = Σ_{i ≤ k} x^i y^{k−i}` (the one-row Schur polynomials in two variables),

  `(Σ_k c^k h_k(x, y) h_k(x', y') X^k) · ∏_{a ∈ {x, y}, b ∈ {x', y'}} (1 − a b c X) = 1 − x y x' y' c² X²`

in `R⟦X⟧`. The one-row part of the Cauchy kernel is the whole kernel divided by
`Σ_j (x y x' y' c²)^j X^{2j}`, because `s_{(p+j, j)}(x, y) = (x y)^j h_p(x, y)`
(`schurV_two_two`); the whole kernel is `cauchy_powerSeries` with `N = m = n = 2`. -/
@[frame_pattern]
theorem oneRow_cauchy_two (x y x' y' c : R) :
    PowerSeries.mk (fun k => c ^ k * (∑ i ∈ range (k + 1), x ^ i * y ^ (k - i))
        * (∑ i ∈ range (k + 1), x' ^ i * y' ^ (k - i)))
      * ((1 - C (x * x' * c) * X) * (1 - C (x * y' * c) * X)
        * (1 - C (y * x' * c) * X) * (1 - C (y * y' * c) * X))
      = 1 - C (x * y * x' * y' * c ^ 2) * X ^ 2 :=
  oneRow_cauchy_two_of (fun α β => cauchy_powerSeries α β le_rfl) x y x' y' c

end GL2

end RMT.Symmetric
