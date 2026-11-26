import RMTlib.Symmetric.SSYT
import RMTlib.Tableaux.JacobiTrudi
import MeaningLib.Frame.Pattern

/-!
# Jacobi–Trudi for semistandard tableaux, evaluated

For values `a : ℕ → R` in a commutative ring, `schurV a N m λ` is the Schur polynomial
`s_λ(a₀, …, a_{m−1})` evaluated: the total weight `∏ a_{T(c)}` of the semistandard tableaux `T`
of shape `λ` (an antitone `Fin N → ℕ`) with entries `< m`, as chains of horizontal strips
(`RMT.Symmetric.Tab`). This file proves that it is the Jacobi–Trudi determinant

  `s_λ(a₀, …, a_{m−1}) = det (h_{λ_i − i + j}(a₀, …, a_{m−1}))_{i, j < N}`

(`schurV_eq_det`), with `h_k` the complete homogeneous symmetric polynomial (`hE`), which is the
evaluation of Mathlib's `MvPolynomial.hsymm` (`hE_eq_sum_sym`). This is the form in which the RH
formalisation *defines* its Schur polynomials (`GlobalTheory.JSW.schur`), so the two definitions
can be identified (bridge `RMTlibBridge.RankinSelberg`).

The proof is by induction on the number of variables `m`. Both sides satisfy the branching rule
in the last variable `t = a_m`:

* tableaux: removing the boxes holding `m` leaves a tableau of an interlacing shape `μ`
  (`λ_{i+1} ≤ μ_i ≤ λ_i`, `RMT.Weyl.GTStep`), so
  `s_λ(a₀, …, a_m) = Σ_μ t^{|λ| − |μ|} s_μ(a₀, …, a_{m−1})` (`schurV_succ`);
* determinants: `h(a₀, …, a_m) = h(t) · h(a₀, …, a_{m−1})` as a product of an `N × W` and a
  `W × N` matrix over a window `W ⊂ ℤ`, and Cauchy–Binet (`det_mul_eq_sum_strictAnti`) expands
  the determinant over decreasing sequences `μ_k − k`. The one-variable factor is a power of `t`
  times the `0/1` staircase determinant, the interlacing indicator of RMTlib's
  `RMT.jacobiTrudi_one_variable` (`det_jtMat_succ`).

## Main results

* `schurV_succ`, `schurV_zero`: the branching rule for tableaux.
* `det_mul_eq_sum_strictAnti`: Cauchy–Binet for an `N × W` times a `W × N` matrix.
* `det_jtMat_succ`, `det_jtMat_zero`: the branching rule for the Jacobi–Trudi determinant.
* `schurV_eq_det`: **Jacobi–Trudi**.
* `hE_eq_sum_sym`: `h_k(a₀, …, a_{m−1}) = Σ_{s ∈ Sym (Fin m) k} ∏_{i ∈ s} a_i`.
-/

open Finset Matrix

namespace RMT.Symmetric

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthSuper (HStrip size)
open RMT.RSK.GrowthBij (IsHChain)


/-- Evaluation of the monomial `x ^ e` at the point `a`. -/
noncomputable def evalMono {ι R : Type*} [CommMonoid R] (a : ι → R) (e : ι →₀ ℕ) : R :=
  e.prod fun i k => a i ^ k

section Eval

variable {ι R : Type*} [CommMonoid R] (a : ι → R)

/-- The empty monomial evaluates to `1`. -/
theorem evalMono_zero : evalMono a 0 = 1 := Finsupp.prod_zero_index

/-- Evaluation is multiplicative. -/
theorem evalMono_add (e f : ι →₀ ℕ) : evalMono a (e + f) = evalMono a e * evalMono a f :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

/-- `x_i ^ k` evaluates to `a_i ^ k`. -/
theorem evalMono_single (i : ι) (k : ℕ) : evalMono a (Finsupp.single i k) = a i ^ k :=
  Finsupp.prod_single_index (pow_zero _)

/-- Evaluation of a sum of exponents is the product of the evaluations. -/
theorem evalMono_sum {κ : Type*} (s : Finset κ) (e : κ → ι →₀ ℕ) :
    evalMono a (∑ x ∈ s, e x) = ∏ x ∈ s, evalMono a (e x) :=
  (Finsupp.prod_finsetSum_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)).symm

/-- `(x_i)^k` evaluates to `a_i ^ k`. -/
theorem evalMono_smul_single (i : ι) (k : ℕ) :
    evalMono a (k • Finsupp.single i 1) = a i ^ k := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one, evalMono_single]

end Eval

variable {N m : ℕ}

/-- The evaluation of a tableau with entries `< m` at `a₀, …, a_{m−1}`: `∏_j a_j ^ #(boxes holding j)`. -/
theorem evalMono_wt {R : Type*} [CommMonoid R] (a : ℕ → R) (T : Tab N m) :
    evalMono a (T.wt id) = ∏ j ∈ range m, a j ^ (size (T.1 (j + 1)) - size (T.1 j)) := by
  rw [Tab.wt, evalMono_sum]
  exact Finset.prod_congr rfl fun j _ => evalMono_smul_single a j _

/-- Tableaux with entries `< m` and shape the vector `l` (padded to `N` rows). -/
abbrev TabV (N m : ℕ) (l : Fin N → ℕ) : Type := {T : Tab N m // T.shape = List.ofFn l}

/-- Finitely many tableaux of each shape (`finite_tab_shape`). -/
noncomputable instance (l : Fin N → ℕ) : Fintype (TabV N m l) := Fintype.ofFinite _

/-- **The Schur polynomial evaluated at a point**: `s_l(a₀, …, a_{m−1})`, the total evaluated
weight of the semistandard tableaux of shape `l` with entries `< m`. -/
noncomputable def schurV {R : Type*} [CommRing R] (a : ℕ → R) (N m : ℕ) (l : Fin N → ℕ) : R :=
  ∑ T : TabV N m l, evalMono a (T.1.wt id)


/-- Entries of `List.ofFn l`, padded by `0`. -/
theorem getD_ofFn (l : Fin N → ℕ) (r : ℕ) :
    (List.ofFn l).getD r 0 = if h : r < N then l ⟨r, h⟩ else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with h <;> simp

/-- A list of length `N` is the list of its entries. -/
theorem ofFn_getD {L : Part} (hL : L.length = N) :
    List.ofFn (fun i : Fin N => L.getD i 0) = L := by
  apply List.ext_getElem (by simp [hL])
  intro r h1 h2
  simp [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- `λ / μ` is a horizontal strip iff `μ` interlaces `λ` (Gelfand–Tsetlin branching). -/
theorem hstrip_ofFn_iff (lam mu : Fin N → ℕ) :
    HStrip (List.ofFn mu) (List.ofFn lam) ↔ Weyl.GTStep lam mu := by
  rw [hstrip_iff]
  simp only [List.length_ofFn, true_and, getD_ofFn]
  constructor
  · intro h
    refine ⟨fun l j hj => ?_, fun t => ?_⟩
    · have := (h l).2
      rw [dite_eq_left (by omega), dite_eq_left l.2] at this
      convert this using 2
      exact Fin.ext hj
    · have := (h t).1
      rwa [dite_eq_left t.2, dite_eq_left t.2] at this
  · rintro ⟨h1, h2⟩ r
    by_cases hr : r < N
    · refine ⟨by rw [dite_eq_left hr, dite_eq_left hr]; exact h2 _, ?_⟩
      rw [dite_eq_left hr]
      split_ifs with hr'
      · exact h1 ⟨r, hr⟩ ⟨r + 1, hr'⟩ rfl
      · exact Nat.zero_le _
    · simp [hr, show ¬ r + 1 < N by omega]

open Classical in
/-- The shapes `μ` interlacing `λ`: `λ_{i+1} ≤ μ_i ≤ λ_i`. -/
noncomputable def interl (lam : Fin N → ℕ) : Finset (Fin N → ℕ) :=
  (Fintype.piFinset fun i => range (lam i + 1)).filter fun mu => Weyl.GTStep lam mu

/-- Membership in `interl`. -/
theorem mem_interl {lam mu : Fin N → ℕ} : mu ∈ interl lam ↔ Weyl.GTStep lam mu := by
  classical
  unfold interl
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨fun i => Finset.mem_range.mpr (Nat.lt_succ_of_le (h.2 i)), h⟩⟩

/-- Extend a tableau with entries `< m` by the strip `L / shape`, filled with `m`. -/
def extendChain (T : Tab N m) (L : Part) : ℕ → Part := fun k => if k ≤ m then T.1 k else L

/-- The extended chain is a chain of horizontal strips. -/
theorem isHChain_extendChain (T : Tab N m) {L : Part} (h : HStrip (T.1 m) L) :
    IsHChain N (m + 1) (extendChain T L) := by
  refine ⟨by simpa [extendChain] using T.2.1.1, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j m with hjm | hjm
  · simp only [extendChain, ite_eq_left hjm.le, ite_eq_left (show j + 1 ≤ m by omega)]
    exact T.2.1.2 j hjm
  · obtain rfl : j = m := by omega
    simpa [extendChain] using h

/-- The tableau `T` extended by the strip `λ / μ` filled with `m`. -/
def extendTab (lam : Fin N → ℕ) (x : Σ mu : interl lam, TabV N m mu.1) : TabV N (m + 1) lam :=
  ⟨⟨extendChain x.2.1 (List.ofFn lam), isHChain_extendChain x.2.1 (by
      rw [show x.2.1.1 m = List.ofFn x.1.1 from x.2.2, hstrip_ofFn_iff]
      exact mem_interl.mp x.1.2),
    fun k hk => by simp [extendChain, show ¬ k ≤ m by omega]⟩,
    by simp [Tab.shape, extendChain]⟩

/-- Extension is a bijection onto the tableaux with entries `< m + 1` of shape `λ`. -/
theorem extendTab_bijective (lam : Fin N → ℕ) :
    Function.Bijective (extendTab (m := m) lam) := by
  constructor
  · rintro ⟨⟨mu, hmu⟩, T⟩ ⟨⟨nu, hnu⟩, T'⟩ h
    have hk : ∀ k, k ≤ m → T.1.1 k = T'.1.1 k := fun k hk => by
      have := congrArg (fun S : TabV N (m + 1) lam => S.1.1 k) h
      simpa [extendTab, extendChain, hk] using this
    have hmn : mu = nu := by
      have := hk m le_rfl
      rw [show T.1.1 m = List.ofFn mu from T.2, show T'.1.1 m = List.ofFn nu from T'.2] at this
      exact List.ofFn_injective this
    subst hmn
    have : T = T' := Subtype.ext (Tab.ext' hk)
    subst this
    rfl
  · intro T
    have hlen := chain_length T.1.2.1 m (Nat.le_succ m)
    set mu : Fin N → ℕ := fun i => (T.1.1 m).getD i 0 with hmudef
    have hmu : List.ofFn mu = T.1.1 m := ofFn_getD hlen
    have hstrip : HStrip (List.ofFn mu) (List.ofFn lam) := by
      have h := T.1.2.1.2 m (Nat.lt_succ_self m)
      rw [show T.1.1 (m + 1) = List.ofFn lam from T.2] at h
      rwa [hmu]
    have hc : IsHChain N m T.1.1 := ⟨T.1.2.1.1, fun j hj => T.1.2.1.2 j (by omega)⟩
    refine ⟨⟨⟨mu, mem_interl.mpr ((hstrip_ofFn_iff lam mu).mp hstrip)⟩,
      ⟨Tab.mk' T.1.1 hc, by simp [Tab.shape, Tab.mk', freeze, hmu]⟩⟩, ?_⟩
    apply Subtype.ext
    apply Tab.ext'
    intro k hk
    simp only [extendTab, extendChain, Tab.mk', freeze]
    split_ifs with hkm
    · rw [Nat.min_eq_left hkm]
    · obtain rfl : k = m + 1 := by omega
      exact T.2.symm

/-- Extension multiplies the weight by `a_m ^ (|λ| − |μ|)`. -/
theorem evalMono_extendTab {R : Type*} [CommRing R] (a : ℕ → R) (lam : Fin N → ℕ)
    (x : Σ mu : interl lam, TabV N m mu.1) :
    evalMono a ((extendTab lam x).1.wt id)
      = a m ^ (∑ i, lam i - ∑ i, x.1.1 i) * evalMono a (x.2.1.wt id) := by
  rw [evalMono_wt, evalMono_wt, Finset.prod_range_succ, mul_comm]
  congr 1
  · simp only [extendTab, extendChain, le_refl, ite_true, show ¬ m + 1 ≤ m by omega, ite_false]
    rw [show x.2.1.1 m = List.ofFn x.1.1 from x.2.2]
    simp [size, List.sum_ofFn]
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    simp only [extendTab, extendChain, ite_eq_left hj.le, ite_eq_left (show j + 1 ≤ m by omega)]

/-- **Branching rule**: removing the boxes holding the largest entry `m`,
`s_λ(a₀, …, a_m) = Σ_{μ interlacing λ} a_m ^ (|λ| − |μ|) s_μ(a₀, …, a_{m−1})`. -/
theorem schurV_succ {R : Type*} [CommRing R] (a : ℕ → R) (lam : Fin N → ℕ) :
    schurV a N (m + 1) lam
      = ∑ mu ∈ interl lam, a m ^ (∑ i, lam i - ∑ i, mu i) * schurV a N m mu := by
  let F : (Σ mu : interl lam, TabV N m mu.1) → R :=
    fun x => a m ^ (∑ i, lam i - ∑ i, x.1.1 i) * evalMono a (x.2.1.wt id)
  calc schurV a N (m + 1) lam = ∑ x, F x := (Fintype.sum_bijective _ (extendTab_bijective lam) _ _
        (fun x => (evalMono_extendTab a lam x).symm)).symm
    _ = ∑ mu : interl lam, ∑ T : TabV N m mu.1, F ⟨mu, T⟩ := Fintype.sum_sigma F
    _ = _ := by
      rw [← Finset.sum_coe_sort (interl lam)]
      simp only [F, schurV, Finset.mul_sum]

/-- With no entries, only the empty shape has a tableau. -/
theorem schurV_zero {R : Type*} [CommRing R] (a : ℕ → R) (lam : Fin N → ℕ) :
    schurV a N 0 lam = if lam = 0 then 1 else 0 := by
  have hsh : ∀ T : Tab N 0, T.shape = zeros N := fun T => T.2.1.1
  have hz : List.ofFn (0 : Fin N → ℕ) = zeros N := by
    exact List.ofFn_const N 0
  split_ifs with h
  · subst h
    have T0 : TabV N 0 0 := ⟨⟨fun _ => zeros N, ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
      fun _ _ => rfl⟩, hz.symm⟩
    have : Subsingleton (TabV N 0 0) := ⟨fun T T' => Subtype.ext (Tab.ext' fun k hk => by
      obtain rfl : k = 0 := by omega
      rw [T.1.2.1.1, T'.1.2.1.1])⟩
    rw [schurV, Fintype.sum_subsingleton _ T0, evalMono_wt]
    simp
  · have : IsEmpty (TabV N 0 lam) := ⟨fun T => h (List.ofFn_injective (by
      rw [hz, ← T.2, hsh])) ⟩
    simp [schurV]


/-! ## Cauchy–Binet -/

section CauchyBinet

variable {R : Type*} [CommRing R]


/-- Expansion of `det (A * B)` over all maps `p : Fin N → W`. -/
theorem det_mul_eq_sum_fun {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (A : Matrix (Fin N) W R) (B : Matrix W (Fin N) R) :
    det (A * B) = ∑ p : Fin N → W, det (A.submatrix id p) * ∏ i, B (p i) i := by
  calc det (A * B)
      = ∑ p : Fin N → W, ∑ σ : Equiv.Perm (Fin N),
          ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (p i) * B (p i) i := by
        simp only [det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
          Fintype.piFinset_univ]
        rw [Finset.sum_comm]
    _ = ∑ p : Fin N → W, det (A.submatrix id p) * ∏ i, B (p i) i := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [det_apply', Finset.sum_mul]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.prod_mul_distrib, mul_assoc]
        rfl

/-- Two decreasing sequences with the same range are equal. -/
theorem strictAnti_range_inj {N : ℕ} {W : Type*} [LinearOrder W] {f g : Fin N → W}
    (hf : StrictAnti f) (hg : StrictAnti g) (h : Set.range f = Set.range g) : f = g := by
  have hf' : StrictMono (f ∘ Fin.rev) := hf.comp Fin.rev_strictAnti
  have hg' : StrictMono (g ∘ Fin.rev) := hg.comp Fin.rev_strictAnti
  have : f ∘ Fin.rev = g ∘ Fin.rev := (hf'.range_inj_of_wellFoundedLT hg').mp (by
    rw [Set.range_comp, Set.range_comp, Fin.rev_surjective.range_eq, Set.image_univ,
      Set.image_univ, h])
  funext i
  simpa using congrFun this (Fin.rev i)

open Classical in
/-- **Cauchy–Binet**: `det (A B) = Σ_S det A[:, S] · det B[S, :]`, the sum over the `N`-element
subsets `S` of `W`, each listed in decreasing order. -/
theorem det_mul_eq_sum_strictAnti {N : ℕ} {W : Type*} [Fintype W] [LinearOrder W]
    (A : Matrix (Fin N) W R) (B : Matrix W (Fin N) R) :
    det (A * B) = ∑ f : {f : Fin N → W // StrictAnti f},
      det (A.submatrix id f.1) * det (B.submatrix f.1 id) := by
  rw [det_mul_eq_sum_fun]
  let e : {f : Fin N → W // StrictAnti f} × Equiv.Perm (Fin N) → (Fin N → W) :=
    fun x => x.1.1 ∘ x.2
  have he : Function.Injective e := by
    rintro ⟨f, τ⟩ ⟨g, τ'⟩ h
    have hfg : f = g := by
      apply Subtype.ext
      apply strictAnti_range_inj f.2 g.2
      have := congrArg Set.range h
      simpa [e, Set.range_comp, τ.surjective.range_eq, τ'.surjective.range_eq] using this
    subst hfg
    refine Prod.ext rfl (Equiv.ext fun i => f.2.injective ?_)
    exact congrFun h i
  symm
  rw [← Fintype.sum_of_injective e he (fun x => det (A.submatrix id (e x)) *
      ∏ i, B (e x i) i) _ ?_ (fun _ => rfl), Fintype.sum_prod_type]
  · refine Finset.sum_congr rfl fun f _ => ?_
    simp only [e]
    have h1 : ∀ τ : Equiv.Perm (Fin N), det (A.submatrix id (f.1 ∘ τ)) =
        ((Equiv.Perm.sign τ : ℤ) : R) * det (A.submatrix id f.1) := fun τ => by
      rw [← det_permute' τ (A.submatrix id f.1)]
      rfl
    simp only [h1]
    rw [det_apply' (B.submatrix f.1 id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Function.comp_apply, submatrix_apply, id]
    ring
  · intro p hp
    by_cases hinj : Function.Injective p
    · exfalso
      apply hp
      set σ := Tuple.sort p
      have hmono : StrictMono (p ∘ σ) :=
        (Tuple.monotone_sort p).strictMono_of_injective (hinj.comp σ.injective)
      let π : Equiv.Perm (Fin N) := Fin.revPerm.trans σ
      refine ⟨(⟨p ∘ π, ?_⟩, π.symm), ?_⟩
      · have : p ∘ π = (p ∘ σ) ∘ Fin.rev := by
          funext i; simp [π]
        rw [this]
        exact hmono.comp_strictAnti Fin.rev_strictAnti
      · funext i; simp [e]
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
        by_contra h
        push Not at h
        exact hinj fun i j hij => h i j hij
      rw [det_zero_of_column_eq hne (fun k => by simp [hij]), zero_mul]

end CauchyBinet

/-! ## The Jacobi–Trudi determinant -/

section JT

variable {R : Type*} [CommRing R]


/-- The complete homogeneous symmetric polynomial `h_k(a₀, …, a_{m−1})`, `0` for `k < 0`. -/
noncomputable def hE (a : ℕ → R) : ℕ → ℤ → R
  | 0, k => if k = 0 then 1 else 0
  | m + 1, k => ∑ r ∈ range (k.toNat + 1), a m ^ r * hE a m (k - r)

/-- `h_k = 0` for `k < 0`. -/
theorem hE_neg (a : ℕ → R) : ∀ (m : ℕ) {k : ℤ}, k < 0 → hE a m k = 0
  | 0, k, hk => by simp [hE, hk.ne]
  | m + 1, k, hk => by rw [hE, Int.toNat_of_nonpos hk.le]; simp [hE_neg a m hk]

/-- The defining sum of `hE` may run over any longer range. -/
theorem hE_succ_eq_sum_range (a : ℕ → R) (m : ℕ) (k : ℤ) {K : ℕ} (hK : k.toNat ≤ K) :
    hE a (m + 1) k = ∑ r ∈ range (K + 1), a m ^ r * hE a m (k - r) := by
  rw [hE]
  refine Finset.sum_subset (fun r hr => by simp at hr ⊢; omega) fun r hr hr' => ?_
  simp only [Finset.mem_range] at hr hr'
  rw [hE_neg a m (by omega), mul_zero]

/-- The entries of `h(a₀, …, a_m) = h(a_m) * h(a₀, …, a_{m−1})` as a matrix product indexed by
`c ∈ [lo, hi]`. -/
theorem sum_Icc_hE (a : ℕ → R) (m : ℕ) (k₀ : ℤ) (j : ℕ) {lo hi : ℤ} (hlo : lo ≤ -j)
    (hlk : lo ≤ k₀) (hhi : k₀ ≤ hi) :
    ∑ c ∈ Icc lo hi, (if c ≤ k₀ then a m ^ (k₀ - c).toNat else 0) * hE a m (c + j)
      = hE a (m + 1) (k₀ + j) := by
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, show (Icc lo hi).filter (· ≤ k₀) = Icc lo k₀ by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega,
    hE_succ_eq_sum_range a m (k₀ + j) (K := (k₀ - lo).toNat) (by omega)]
  refine Finset.sum_nbij' (fun c => (k₀ - c).toNat) (fun r => k₀ - r) ?_ ?_ ?_ ?_ ?_
  · intro c hc; simp only [Finset.mem_Icc, Finset.mem_range] at hc ⊢; omega
  · intro r hr; simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢; omega
  · intro c hc; simp only [Finset.mem_Icc] at hc; omega
  · intro r hr; simp only [Finset.mem_range] at hr; omega
  · intro c hc; simp only [Finset.mem_Icc] at hc
    congr 2; omega

/-- `Σ toNat = toNat Σ` for nonnegative integers. -/
theorem sum_toNat {N : ℕ} (x : Fin N → ℤ) (hx : ∀ k, 0 ≤ x k) :
    ∑ k, (x k).toNat = (∑ k, x k).toNat := by
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sum, Int.toNat_of_nonneg (Finset.sum_nonneg fun k _ => hx k)]
  exact Finset.sum_congr rfl fun k _ => Int.toNat_of_nonneg (hx k)

/-- Powers of `t` along a staircase factor out of the determinant. -/
theorem det_pow_staircase {N : ℕ} (t : R) (u v : Fin N → ℤ) :
    det (of fun i k => if v k ≤ u i then t ^ (u i - v k).toNat else 0)
      = t ^ (∑ i, u i - ∑ k, v k).toNat * det (of fun i k => if v k ≤ u i then (1 : R) else 0) := by
  rw [det_apply', det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_left_comm]
  congr 1
  simp only [of_apply]
  by_cases h : ∀ k, v k ≤ u (σ k)
  · simp only [h, ite_true, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [sum_toNat _ (fun k => by have := h k; omega), Finset.sum_sub_distrib,
      Equiv.sum_comp σ u]
  · push Not at h
    obtain ⟨k, hk⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk.not_ge]),
      Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk.not_ge]), mul_zero]

open Classical in
/-- The `0/1` staircase of the one-variable skew Jacobi–Trudi matrix, over any commutative ring:
its determinant is the interlacing indicator. -/
theorem det_staircase_gtStep {N : ℕ} (lam mu : Fin N → ℕ) (hl : Antitone lam) (hm : Antitone mu) :
    det (of fun i k : Fin N => if (mu k : ℤ) - k ≤ (lam i : ℤ) - i then (1 : R) else 0)
      = if Weyl.GTStep lam mu then 1 else 0 := by
  classical
  set M : Matrix (Fin N) (Fin N) ℤ :=
    of fun i k => if (mu k : ℤ) - k ≤ (lam i : ℤ) - i then 1 else 0 with hM
  have hQ : ((det M : ℤ) : ℚ) = if Weyl.GTStep lam mu then 1 else 0 := by
    rw [← jacobiTrudi_one_variable lam mu hl hm]
    have := RingHom.map_det (Int.castRingHom ℚ) M
    simp only [eq_intCast] at this
    rw [this]
    congr 1
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hM, of_apply, hOne_one]
    split_ifs <;> first | omega | simp
  have hZ : det M = if Weyl.GTStep lam mu then 1 else 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [hQ]; split_ifs <;> simp
  have := congrArg (Int.castRingHom R) hZ
  rw [RingHom.map_det] at this
  convert this using 2
  · ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hM, of_apply]
    split_ifs <;> simp
  · split_ifs <;> simp


/-- The Jacobi–Trudi matrix `(h_{l_i − i + j}(a₀, …, a_{m−1}))_{i, j < N}`. -/
noncomputable def jtMat (a : ℕ → R) (m : ℕ) (l : Fin N → ℕ) : Matrix (Fin N) (Fin N) R :=
  of fun i j => hE a m ((l i : ℤ) - i + j)

/-- A decreasing integer sequence drops by at least one per step. -/
theorem strictAnti_add_le {f : Fin N → ℤ} (hf : StrictAnti f) :
    ∀ (d : ℕ) (k : Fin N) (h : k.1 + d < N), f ⟨k + d, h⟩ + ((k + d : ℕ) : ℤ) ≤ f k + k
  | 0, k, h => by simp
  | d + 1, k, h => by
    have h1 := strictAnti_add_le hf d k (by omega)
    have h2 := hf (show (⟨k + d, by omega⟩ : Fin N) < ⟨k + (d + 1), h⟩ from
      Fin.mk_lt_mk.mpr (by omega))
    push_cast at h1 ⊢
    omega

/-- A shape interlacing an antitone `λ` is antitone. -/
theorem antitone_of_gtStep {lam mu : Fin N → ℕ} (hl : Antitone lam) (h : Weyl.GTStep lam mu) :
    Antitone mu := by
  intro k k' hkk'
  rcases eq_or_lt_of_le hkk' with rfl | hlt
  · exact le_rfl
  · have hlt' : (k : ℕ) < k' := hlt
    have h1 := h.2 k'
    have h2 := h.1 k ⟨k + 1, by omega⟩ rfl
    have h3 := hl (show (⟨k + 1, by omega⟩ : Fin N) ≤ k' from Fin.mk_le_mk.mpr (by omega))
    omega

open Classical in
/-- **Branching of the Jacobi–Trudi determinant**: with `t = a_m`,
`det h(a₀, …, a_m)_λ = Σ_{μ interlacing λ} t ^ (|λ| − |μ|) det h(a₀, …, a_{m−1})_μ`.
The matrix factors as `h(t) · h(a₀, …, a_{m−1})` over the window `c ∈ [−N, |λ|]`; Cauchy–Binet
expands the determinant over decreasing `c = μ_k − k`, and the one-variable factor is the
interlacing indicator. -/
theorem det_jtMat_succ (a : ℕ → R) (m : ℕ) (lam : Fin N → ℕ) (hl : Antitone lam) :
    det (jtMat a (m + 1) lam)
      = ∑ mu ∈ interl lam, a m ^ (∑ i, lam i - ∑ i, mu i) * det (jtMat a m mu) := by
  set t := a m
  set S : ℤ := ∑ i, (lam i : ℤ) with hS
  have hlamS : ∀ i, (lam i : ℤ) ≤ S := fun i =>
    Finset.single_le_sum (f := fun i => (lam i : ℤ)) (fun _ _ => by positivity) (Finset.mem_univ i)
  let A : Matrix (Fin N) (Icc (-(N : ℤ)) S) R := of fun i c =>
    if (c : ℤ) ≤ (lam i : ℤ) - i then t ^ ((lam i : ℤ) - i - c).toNat else 0
  let B : Matrix (Icc (-(N : ℤ)) S) (Fin N) R := of fun c j => hE a m (c + j)
  have hAB : jtMat a (m + 1) lam = A * B := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [A, B, of_apply, jtMat]
    rw [Finset.sum_coe_sort (Icc (-(N : ℤ)) S) (fun c => (if c ≤ (lam i : ℤ) - i then
      t ^ ((lam i : ℤ) - i - c).toNat else 0) * hE a m (c + j)),
      sum_Icc_hE a m _ j (by omega) (by omega) (by have := hlamS i; omega)]
  -- the decreasing sequence `μ_k − k`
  have hmem : ∀ mu ∈ interl lam, ∀ k : Fin N, (mu k : ℤ) - k ∈ Icc (-(N : ℤ)) S := by
    intro mu hmu k
    have := (mem_interl.mp hmu).2 k
    have := hlamS k
    simp only [Finset.mem_Icc]
    omega
  have hsa : ∀ mu (hmu : mu ∈ interl lam),
      StrictAnti (fun k : Fin N => (⟨(mu k : ℤ) - k, hmem mu hmu k⟩ : Icc (-(N : ℤ)) S)) := by
    intro mu hmu k k' hkk'
    have := antitone_of_gtStep hl (mem_interl.mp hmu) hkk'.le
    have : (k : ℕ) < k' := hkk'
    show (mu k' : ℤ) - k' < (mu k : ℤ) - k
    omega
  let iμ : ∀ mu, mu ∈ interl lam → {f : Fin N → Icc (-(N : ℤ)) S // StrictAnti f} :=
    fun mu hmu => ⟨fun k => ⟨(mu k : ℤ) - k, hmem mu hmu k⟩, hsa mu hmu⟩
  have hdetA : ∀ f : Fin N → Icc (-(N : ℤ)) S, det (A.submatrix id f)
      = t ^ (∑ i, ((lam i : ℤ) - i) - ∑ k, (f k : ℤ)).toNat
        * det (of fun i k => if (f k : ℤ) ≤ (lam i : ℤ) - i then (1 : R) else 0) :=
    fun f => det_pow_staircase t (fun i => (lam i : ℤ) - i) (fun k => (f k : ℤ))
  have hval : ∀ mu (hmu : mu ∈ interl lam), t ^ (∑ i, lam i - ∑ i, mu i) * det (jtMat a m mu)
      = det (A.submatrix id (iμ mu hmu).1) * det (B.submatrix (iμ mu hmu).1 id) := by
    intro mu hmu
    have hg := mem_interl.mp hmu
    rw [hdetA, det_staircase_gtStep lam mu hl (antitone_of_gtStep hl hg), ite_eq_left hg, mul_one]
    congr 2
    have hle : ∑ i, mu i ≤ ∑ i, lam i := Finset.sum_le_sum fun i _ => hg.2 i
    have : (∑ i, ((lam i : ℤ) - i) - ∑ k, ((iμ mu hmu).1 k : ℤ))
        = ((∑ i, lam i - ∑ i, mu i : ℕ) : ℤ) := by
      simp only [iμ, Finset.sum_sub_distrib]
      push_cast [Nat.cast_sub hle]
      ring
    rw [this, Int.toNat_natCast]
  rw [hAB, det_mul_eq_sum_strictAnti]
  symm
  refine Finset.sum_bij_ne_zero (fun mu hmu _ => iμ mu hmu) (fun _ _ _ => Finset.mem_univ _)
    ?_ ?_ (fun mu hmu _ => hval mu hmu)
  · intro mu hmu _ nu hnu _ h
    funext k
    have := congrArg (fun f : {f : Fin N → Icc (-(N : ℤ)) S // StrictAnti f} => (f.1 k : ℤ)) h
    simp only [iμ] at this
    omega
  · intro f _ hf
    have hB : det (B.submatrix f.1 id) ≠ 0 := right_ne_zero_of_mul hf
    have hA : det (A.submatrix id f.1) ≠ 0 := left_ne_zero_of_mul hf
    have hf' : StrictAnti fun k => ((f.1 k : Icc (-(N : ℤ)) S) : ℤ) := fun k k' h => f.2 h
    have hnn : ∀ k : Fin N, 0 ≤ (f.1 k : ℤ) + k := by
      intro k
      by_contra hneg
      push Not at hneg
      have hL := strictAnti_add_le hf' (N - 1 - k) k (by omega)
      apply hB
      apply det_eq_zero_of_row_eq_zero ⟨k + (N - 1 - k), by omega⟩
      intro j
      simp only [B, submatrix_apply, of_apply, id]
      apply hE_neg
      have := j.2
      push_cast at hL
      omega
    set mu : Fin N → ℕ := fun k => ((f.1 k : ℤ) + k).toNat with hmudef
    have hmuf : ∀ k, (mu k : ℤ) - k = f.1 k := fun k => by
      simp only [hmudef]; have := hnn k; omega
    have hmuA : Antitone mu := by
      intro k k' hkk'
      have hkk : (k : ℕ) ≤ k' := hkk'
      have := strictAnti_add_le hf' (k' - k) k (by omega)
      simp only [show (k : ℕ) + (k' - k) = k' by omega, Fin.eta] at this
      simp only [hmudef]
      have := hnn k; have := hnn k'
      omega
    have hg : Weyl.GTStep lam mu := by
      by_contra hng
      apply hA
      rw [hdetA]
      have := det_staircase_gtStep (R := R) lam mu hl hmuA
      rw [ite_eq_right hng] at this
      rw [show (of fun i k => if (f.1 k : ℤ) ≤ (lam i : ℤ) - i then (1 : R) else 0)
        = of fun i k : Fin N => if (mu k : ℤ) - k ≤ (lam i : ℤ) - i then (1 : R) else 0 from by
          ext i k; simp only [of_apply, hmuf], this, mul_zero]
    have hmu : mu ∈ interl lam := mem_interl.mpr hg
    have hfeq : iμ mu hmu = f := by
      apply Subtype.ext; funext k; apply Subtype.ext; exact hmuf k
    refine ⟨mu, hmu, ?_, hfeq⟩
    rw [hval mu hmu, hfeq]
    exact hf

/-- At `m = 0` the Jacobi–Trudi determinant is `1` at the empty shape and `0` otherwise. -/
theorem det_jtMat_zero (a : ℕ → R) (lam : Fin N → ℕ) (hl : Antitone lam) :
    det (jtMat a 0 lam) = if lam = 0 then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [show jtMat a 0 (0 : Fin N → ℕ) = 1 from by
      ext i j
      simp only [jtMat, hE, Pi.zero_apply, CharP.cast_eq_zero, zero_sub, of_apply, Matrix.one_apply]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; apply h2; ext; omega) | (exfalso; subst h2; omega)]
    exact det_one
  · obtain ⟨i, hi⟩ : ∃ i, lam i ≠ 0 := by
      by_contra hc; push Not at hc; exact h (funext hc)
    have h0 : 0 < N := Fin.pos i
    apply det_eq_zero_of_row_eq_zero ⟨0, h0⟩
    intro j
    have := hl (show (⟨0, h0⟩ : Fin N) ≤ i from Fin.mk_le_mk.mpr (Nat.zero_le _))
    simp only [jtMat, hE, of_apply]
    rw [ite_eq_right (by push_cast; omega)]

/-- **The Jacobi–Trudi identity for semistandard tableaux**: for an antitone `λ : Fin N → ℕ`,
the evaluated Schur polynomial `s_λ(a₀, …, a_{m−1})` (total weight of the semistandard tableaux
of shape `λ` with entries `< m`) is `det (h_{λ_i − i + j}(a₀, …, a_{m−1}))_{i, j < N}`.
Both sides satisfy the branching rule in the last variable (`schurV_succ`, `det_jtMat_succ`). -/
@[frame_pattern]
theorem schurV_eq_det (a : ℕ → R) : ∀ (m : ℕ) (lam : Fin N → ℕ), Antitone lam →
    schurV a N m lam = det (jtMat a m lam)
  | 0, lam, hl => by rw [schurV_zero, det_jtMat_zero a lam hl]
  | m + 1, lam, hl => by
    rw [schurV_succ, det_jtMat_succ a m lam hl]
    refine Finset.sum_congr rfl fun mu hmu => ?_
    rw [schurV_eq_det a m mu (antitone_of_gtStep hl (mem_interl.mp hmu))]

/-- `h_k` as a sum over compositions. -/
theorem hE_eq_sum_antidiagonalTuple (a : ℕ → R) : ∀ (m k : ℕ),
    hE a m k = ∑ P ∈ Finset.Nat.antidiagonalTuple m k, ∏ i : Fin m, a i ^ P i
  | 0, 0 => by simp [hE]
  | 0, k + 1 => by simp [hE]; omega
  | m + 1, k => by
    rw [hE, Int.toNat_natCast]
    have hr : ∀ r ∈ range (k + 1), a m ^ r * hE a m ((k : ℤ) - r)
        = ∑ Q ∈ Finset.Nat.antidiagonalTuple m (k - r), a m ^ r * ∏ i : Fin m, a i ^ Q i := by
      intro r hr
      rw [show (k : ℤ) - r = ((k - r : ℕ) : ℤ) by
        have := Finset.mem_range.mp hr; push_cast [Nat.cast_sub (by omega : r ≤ k)]; ring,
        hE_eq_sum_antidiagonalTuple a m (k - r), Finset.mul_sum]
    rw [Finset.sum_congr rfl hr, Finset.sum_sigma']
    refine Finset.sum_nbij' (fun x => Fin.snoc x.2 x.1) (fun P => ⟨P (Fin.last m), Fin.init P⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨r, Q⟩ h
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple] at h
      simp only [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last]
      omega
    · intro P h
      simp only [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_castSucc] at h
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple, Fin.init]
      omega
    · rintro ⟨r, Q⟩ _
      simp [Fin.init_snoc]
    · intro P _
      simp [Fin.snoc_init_self]
    · rintro ⟨r, Q⟩ _
      simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc,
        Fin.val_last]
      ring

/-- **`h_k` is Mathlib's complete homogeneous symmetric polynomial**, evaluated:
`hE a m k = Σ_{s ∈ Sym (Fin m) k} ∏_{i ∈ s} a_i` (the evaluation of `MvPolynomial.hsymm`). -/
@[frame_pattern]
theorem hE_eq_sum_sym (a : ℕ → R) (m k : ℕ) :
    hE a m k = ∑ s : Sym (Fin m) k, (s.1.map fun i : Fin m => a i.1).prod := by
  classical
  rw [hE_eq_sum_antidiagonalTuple]
  let e := Sym.equivNatSumOfFintype (Fin m) k
  refine Finset.sum_bij' (fun P hP => e.symm ⟨P, Finset.Nat.mem_antidiagonalTuple.mp hP⟩)
    (fun s _ => (e s).1) (fun _ _ => Finset.mem_univ _)
    (fun s _ => Finset.Nat.mem_antidiagonalTuple.mpr (e s).2) (fun P hP => by simp)
    (fun s _ => by simp) ?_
  intro P hP
  have h1 : ((e.symm ⟨P, Finset.Nat.mem_antidiagonalTuple.mp hP⟩ : Sym (Fin m) k) : Multiset (Fin m))
      = ∑ i, P i • {i} := Sym.coe_equivNatSumOfFintype_symm_apply _ _ _
  show _ = (Multiset.map (fun i : Fin m => a i.1)
    ((e.symm ⟨P, Finset.Nat.mem_antidiagonalTuple.mp hP⟩ : Sym (Fin m) k) : Multiset (Fin m))).prod
  have h2 := map_sum (Multiset.mapAddMonoidHom (fun i : Fin m => a i.1))
    (fun i => P i • ({i} : Multiset (Fin m))) Finset.univ
  simp only [Multiset.mapAddMonoidHom_apply] at h2
  rw [h1, h2, Multiset.prod_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton, Multiset.prod_singleton]

end JT

end RMT.Symmetric
