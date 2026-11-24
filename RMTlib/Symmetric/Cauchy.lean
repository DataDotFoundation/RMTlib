import RMTlib.Symmetric.ValuedSet
import RMTlib.RSK.GrowthBij

/-!
# The Cauchy identity as a weight-preserving bijection

The bosonic growth diagram (`RMT.RSK.GrowthBij`) is turned into an equivalence of types
`rskEquiv` between `ℕ`-matrices with `n` rows and `m` columns and pairs of semistandard tableaux
of the same shape, the first with entries `< m`, the second with entries `< n`. It sends the
weight `∏ (x_j y_i) ^ (A i j)` of a matrix to the weight `x ^ P y ^ Q` of the pair. Summing
weights on both sides (as valued sets, `RMT.Symmetric.ValuedSet`) gives the Cauchy identity

  `∑' λ, s_λ(x₀, …, x_{m−1}) s_λ(y₀, …, y_{n−1}) = ∑' A, ∏_{i,j} (x_j y_i) ^ (A i j)`

in `MvPowerSeries ι R` with the product topology, for any two families of variables
`x y : ℕ → ι` (`cauchy`). The right side is the expansion of `∏_{i<n, j<m} (1 − x_j y_i)⁻¹`.

Tableaux are chains of horizontal strips of padded shapes with `N` rows (`Tab N m`), as in
`RMT.RSK.GrowthBij`; the Schur polynomial `schur x N m λ` is the total weight of the tableaux
of shape `λ`, a finite sum (`finite_tab_shape`). The identity needs `m ≤ N` (enough rows for
every shape that occurs).

## Main definitions

* `Tab N m`: semistandard tableaux with entries `< m` and at most `N` rows, as chains
  `c 0 = ∅ ⊆ c 1 ⊆ … ⊆ c m` of horizontal strips, frozen after `m`.
* `Tab.wt x T`: the content of `T` in the variables `x`, `Σ_j #(boxes holding j) • x_j`.
* `schur x N m λ`: `∑' T : Tab N m of shape λ, X ^ (wt x T)`.
* `matWt x y A`: `Σ_{i,j} A i j • (x_j + y_i)`.
* `rskEquiv`: matrices `≃` pairs of tableaux of the same shape.

## Main results

* `wt_rskEquiv`: `rskEquiv` preserves weights.
* `finiteFibres_matWt`: matrices of a given weight are finitely many.
* `cauchy`: the Cauchy identity in `m` and `n` variables, with summability of both sides
  (`summable_matWt`, `summable_schur_mul_schur`).
* `tsum_matWt_eq_prod`, `cauchy_prod`: the total weight of the matrices is
  `∏_{i,j} Σ' t, (x_j y_i) ^ t`, so `(∏_{i<n, j<m} (1 − x_j y_i)) · Σ' λ, s_λ(x) s_λ(y) = 1`.
-/

open scoped MvPowerSeries.WithPiTopology
open MvPowerSeries

namespace RMT.Symmetric

open RMT.RSK.Growth (Part zeros)
open RMT.RSK.GrowthGeneric (grow backEntry back)
open RMT.RSK.GrowthSuper (HStrip size rowSum colSum RelL Strip)
open RMT.RSK.GrowthBij

/-! ## Tableaux as frozen chains -/

/-- `c` frozen after `m`: `c k` for `k ≤ m`, then `c m`. -/
def freeze (m : ℕ) (c : ℕ → Part) : ℕ → Part := fun k => c (min k m)

/-- Semistandard tableaux with entries `< m` and at most `N` rows: chains of horizontal strips
from the empty shape with `N` (padded) rows, the boxes of `c (j+1) / c j` holding `j`, frozen
after `m`. -/
abbrev Tab (N m : ℕ) : Type := {c : ℕ → Part // IsHChain N m c ∧ ∀ k, m ≤ k → c k = c m}

variable {N n m : ℕ}

/-- The shape of a tableau. -/
def Tab.shape (T : Tab N m) : Part := T.1 m

/-- The content of a tableau in the variables `x`: the number of boxes holding `j` is the
exponent of `x j`. -/
noncomputable def Tab.wt {ι : Type*} (x : ℕ → ι) (T : Tab N m) : ι →₀ ℕ :=
  ∑ j ∈ Finset.range m, (size (T.1 (j + 1)) - size (T.1 j)) • Finsupp.single (x j) 1

theorem isHChain_freeze {c : ℕ → Part} (h : IsHChain N m c) : IsHChain N m (freeze m c) := by
  refine ⟨by simpa [freeze] using h.1, fun j hj => ?_⟩
  simp only [freeze, Nat.min_eq_left (Nat.le_of_lt hj), Nat.min_eq_left hj]
  exact h.2 j hj

theorem freeze_frozen (c : ℕ → Part) (k : ℕ) (hk : m ≤ k) : freeze m c k = freeze m c m := by
  simp [freeze, Nat.min_eq_right hk]

/-- Freeze a chain into a tableau. -/
def Tab.mk' (c : ℕ → Part) (h : IsHChain N m c) : Tab N m :=
  ⟨freeze m c, isHChain_freeze h, freeze_frozen c⟩

theorem Tab.eq_min (T : Tab N m) (k : ℕ) : T.1 k = T.1 (min k m) := by
  rcases Nat.le_total k m with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, T.2.2 k h]

theorem Tab.ext' {T T' : Tab N m} (h : ∀ k, k ≤ m → T.1 k = T'.1 k) : T = T' := by
  apply Subtype.ext
  funext k
  rw [T.eq_min, T'.eq_min]
  exact h _ (Nat.min_le_right _ _)

/-! ## Finitely many tableaux of a given shape -/

theorem size_le_of_relL : ∀ {a b : Part}, RelL false a b → size a ≤ size b
  | [], [], _ => Nat.le_refl _
  | x :: a, y :: b, ⟨hxy, h⟩ => by
    have := size_le_of_relL h
    simp only [RMT.RSK.GrowthSuper.Rel] at hxy
    simp only [RMT.RSK.GrowthSuper.size_cons]
    omega
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem le_size_of_mem : ∀ {l : Part} {x : ℕ}, x ∈ l → x ≤ size l
  | y :: l, x, h => by
    simp only [RMT.RSK.GrowthSuper.size_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_size_of_mem h
      omega

/-- Along a chain, shapes have `N` rows. -/
theorem chain_length {c : ℕ → Part} (h : IsHChain N m c) : ∀ k, k ≤ m → (c k).length = N
  | 0, _ => by rw [h.1]; simp [zeros]
  | k + 1, hk => by
    rw [← HStrip.length_eq (h.2 k hk)]
    exact chain_length h k (by omega)

/-- Along a chain, shapes grow in size. -/
theorem chain_size {c : ℕ → Part} (h : IsHChain N m c) :
    ∀ d k, k + d = m → size (c k) ≤ size (c m)
  | 0, k, hk => by rw [← hk]; exact Nat.le_refl _
  | d + 1, k, hk => by
    have := chain_size h d (k + 1) (by omega)
    have := size_le_of_relL (Strip.relL (p := false) (h.2 k (by omega)))
    omega

/-- Lists of length `N` with entries at most `B` are finitely many. -/
theorem finite_bounded (N B : ℕ) : {l : Part | l.length = N ∧ ∀ x ∈ l, x ≤ B}.Finite := by
  apply (Set.finite_range (fun f : Fin N → Fin (B + 1) => List.ofFn (fun i => (f i : ℕ)))).subset
  rintro l ⟨hl, hb⟩
  subst hl
  exact ⟨fun i => ⟨l[i], Nat.lt_succ_of_le (hb _ (List.getElem_mem _))⟩, by simp⟩

/-- **Finitely many tableaux of each shape.** -/
instance finite_tab_shape (lam : Part) : Finite {T : Tab N m // T.shape = lam} := by
  have hS : (Set.univ.pi (fun _ : Fin (m + 1) =>
      {l : Part | l.length = N ∧ ∀ x ∈ l, x ≤ size lam})).Finite :=
    Set.Finite.pi (fun _ => finite_bounded N (size lam))
  have := hS.to_subtype
  refine Finite.of_injective
    (β := ↥(Set.univ.pi (fun _ : Fin (m + 1) => {l : Part | l.length = N ∧ ∀ x ∈ l, x ≤ size lam})))
    (fun T => ⟨fun k => T.1.1 k, ?_⟩) ?_
  · intro k _
    have hk : (k : ℕ) ≤ m := Nat.lt_succ_iff.mp k.2
    have h1 := chain_length T.1.2.1 k hk
    have h2 := chain_size T.1.2.1 (m - k) k (by omega)
    have hsh : T.1.1 m = lam := T.2
    rw [hsh] at h2
    exact ⟨h1, fun x hx => Nat.le_trans (le_size_of_mem hx) h2⟩
  · intro T T' h
    apply Subtype.ext
    apply Tab.ext'
    intro k hk
    exact congrFun (congrArg Subtype.val h) ⟨k, Nat.lt_succ_of_le hk⟩

/-- **The Schur polynomial** `s_λ(x₀, …, x_{m−1})`: the total weight of the semistandard
tableaux of shape `λ` with entries `< m`, in the variables `x`. Shapes are padded to `N` rows. -/
noncomputable def schur {ι : Type*} (R : Type*) [CommSemiring R] [TopologicalSpace R]
    (x : ℕ → ι) (N m : ℕ) (lam : Part) : MvPowerSeries ι R :=
  ∑' T : {T : Tab N m // T.shape = lam}, mono (T.1.wt x)

/-! ## Matrices -/

/-- The weight of a matrix: `Σ_{i,j} A i j • (x_j + y_i)`, that is `∏ (x_j y_i) ^ (A i j)`. -/
noncomputable def matWt {ι : Type*} (x y : ℕ → ι) (A : Fin n → Fin m → ℕ) : ι →₀ ℕ :=
  ∑ i : Fin n, ∑ j : Fin m, A i j • (Finsupp.single (x j) 1 + Finsupp.single (y i) 1)

/-- A matrix as a filling of `ℕ × ℕ`, zero outside the rectangle. -/
def extM (A : Fin n → Fin m → ℕ) : ℕ → ℕ → ℕ :=
  fun i j => if h : i < n ∧ j < m then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

theorem le_matWt {ι : Type*} (x y : ℕ → ι) (A : Fin n → Fin m → ℕ) (i : Fin n) (j : Fin m) :
    A i j ≤ matWt x y A (x j) := by
  classical
  simp only [matWt, Finsupp.coe_finsetSum, Finset.sum_apply]
  have h1 : A i j ≤ (A i j • (Finsupp.single (x j) 1 + Finsupp.single (y i) 1) : ι →₀ ℕ) (x j) := by
    simp only [Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_eq_same, smul_eq_mul]
    exact Nat.le_mul_of_pos_right _ (by omega)
  refine Nat.le_trans h1 (Nat.le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)))
  exact Finset.single_le_sum (f := fun j' => (A i j' • (Finsupp.single (x j') 1
    + Finsupp.single (y i) 1) : ι →₀ ℕ) (x j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

/-- **Matrices of a given weight are finitely many.** -/
theorem finiteFibres_matWt {ι : Type*} (x y : ℕ → ι) :
    FiniteFibres (matWt (n := n) (m := m) x y) := by
  intro d
  refine (Set.Finite.pi (fun i : Fin n => Set.Finite.pi
    (fun j : Fin m => Set.finite_Iic (d (x j))))).subset ?_
  intro A hA
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]
  intro i j
  have hA' : matWt x y A = d := hA
  rw [← hA']
  exact le_matWt x y A i j

/-! ## The RSK equivalence -/

/-- Pairs of tableaux of the same shape, the first with entries `< m`, the second `< n`. -/
def Pairs (N n m : ℕ) : Type := {pq : Tab N m × Tab N n // pq.1.shape = pq.2.shape}

/-- The weight `x ^ P y ^ Q` of a pair. -/
noncomputable def Pairs.wt {ι : Type*} (x y : ℕ → ι) (pq : Pairs N n m) : ι →₀ ℕ :=
  pq.1.1.wt x + pq.1.2.wt y

/-- RSK: the top and right edges of the growth diagram. -/
def rskFwd (A : Fin n → Fin m → ℕ) : Pairs N n m :=
  ⟨(Tab.mk' (fun j => grow Fb (zeros N) (extM A) n j) (isHChain_top _ N n m),
    Tab.mk' (fun i => grow Fb (zeros N) (extM A) i m) (isHChain_right _ N n m)), by
    simp [Tab.shape, Tab.mk', freeze]⟩

/-- Inverse RSK: the entries read off by the backward growth diagram. -/
def rskBwd (pq : Pairs N n m) : Fin n → Fin m → ℕ :=
  fun i j => backEntry Bb pq.1.1.1 pq.1.2.1 n m i j

theorem backEntry_congr (top right top' right' : ℕ → Part)
    (ht : ∀ j, j ≤ m → top j = top' j) (hr : ∀ i, i ≤ n → right i = right' i) (i j : ℕ)
    (hi : i < n) (hj : j < m) :
    backEntry Bb top right n m i j = backEntry Bb top' right' n m i j := by
  unfold backEntry
  have hb := RMT.RSK.GrowthGeneric.back_congr Bb n m top right top' right' ht hr
  rw [hb (i + 1) j (by omega) (by omega), hb i (j + 1) (by omega) (by omega),
    hb (i + 1) (j + 1) (by omega) (by omega)]

/-- **The RSK correspondence** (Knuth), in growth-diagram form: `ℕ`-matrices with `n` rows and
`m` columns are in bijection with pairs of semistandard tableaux of the same shape with entries
`< m` and `< n`, for shapes with `N ≥ m` rows. -/
def rskEquiv (hm : m ≤ N) : (Fin n → Fin m → ℕ) ≃ Pairs N n m where
  toFun := rskFwd
  invFun := rskBwd
  left_inv A := by
    funext i j
    simp only [rskBwd, rskFwd, Tab.mk']
    rw [backEntry_congr _ _ (fun j => grow Fb (zeros N) (extM A) n j)
      (fun i => grow Fb (zeros N) (extM A) i m)
      (fun j hj => by simp [freeze, Nat.min_eq_left hj])
      (fun i hi => by simp [freeze, Nat.min_eq_left hi]) i j i.2 j.2,
      backEntry_edges (extM A) N n m hm i j i.2 j.2]
    simp [extM]
  right_inv pq := by
    obtain ⟨⟨P, Q⟩, hc⟩ := pq
    have hc' : P.1 m = Q.1 n := hc
    have hg : ∀ i j, i ≤ n → j ≤ m →
        grow Fb (zeros N) (extM (rskBwd (⟨(P, Q), hc⟩ : Pairs N n m))) i j
          = grow Fb (zeros N) (backEntry Bb P.1 Q.1 n m) i j :=
      grow_congr _ _ _ _ n m (fun i j hi hj => by simp [extM, hi, hj, rskBwd])
    apply Subtype.ext
    apply Prod.ext
    · apply Tab.ext'
      intro k hk
      simp only [rskFwd, Tab.mk', freeze, Nat.min_eq_left hk]
      rw [hg n k (Nat.le_refl _) hk, top_backEntry P.2.1 Q.2.1 hc' k hk]
    · apply Tab.ext'
      intro k hk
      simp only [rskFwd, Tab.mk', freeze, Nat.min_eq_left hk]
      rw [hg k m hk (Nat.le_refl _), right_backEntry P.2.1 Q.2.1 hc' k hk]

theorem colSum_eq (σ : ℕ → ℕ → ℕ) (j : ℕ) : ∀ k, colSum σ j k = ∑ i ∈ Finset.range k, σ i j
  | 0 => rfl
  | k + 1 => by rw [Finset.sum_range_succ, ← colSum_eq σ j k]; rfl

theorem rowSum_eq (σ : ℕ → ℕ → ℕ) (i : ℕ) : ∀ k, rowSum σ i k = ∑ j ∈ Finset.range k, σ i j
  | 0 => rfl
  | k + 1 => by rw [Finset.sum_range_succ, ← rowSum_eq σ i k]; rfl

theorem wt_fst {ι : Type*} (x : ℕ → ι) (hm : m ≤ N) (A : Fin n → Fin m → ℕ) :
    (rskFwd (N := N) A).1.1.wt x = ∑ i : Fin n, ∑ j : Fin m, A i j • Finsupp.single (x j) 1 := by
  have key : ∀ j ∈ Finset.range m,
      (size ((rskFwd (N := N) A).1.1.1 (j + 1)) - size ((rskFwd (N := N) A).1.1.1 j))
        • Finsupp.single (x j) 1
      = (∑ i ∈ Finset.range n, extM A i j) • Finsupp.single (x j) 1 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [rskFwd, Tab.mk', freeze, Nat.min_eq_left hj', Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [size_top_succ (extM A) N n m hm j hj', colSum_eq]
    congr 1
    omega
  rw [Tab.wt, Finset.sum_congr rfl key,
    Finset.sum_range (fun j => (∑ i ∈ Finset.range n, extM A i j) • Finsupp.single (x j) 1)]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_range (fun i => extM A i j), Finset.sum_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [extM]

theorem wt_snd {ι : Type*} (y : ℕ → ι) (hm : m ≤ N) (A : Fin n → Fin m → ℕ) :
    (rskFwd (N := N) A).1.2.wt y = ∑ i : Fin n, ∑ j : Fin m, A i j • Finsupp.single (y i) 1 := by
  have key : ∀ i ∈ Finset.range n,
      (size ((rskFwd (N := N) A).1.2.1 (i + 1)) - size ((rskFwd (N := N) A).1.2.1 i))
        • Finsupp.single (y i) 1
      = (∑ j ∈ Finset.range m, extM A i j) • Finsupp.single (y i) 1 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [rskFwd, Tab.mk', freeze, Nat.min_eq_left hi', Nat.min_eq_left (Nat.le_of_lt hi')]
    rw [size_right_succ (extM A) N n m hm i hi', rowSum_eq]
    congr 1
    omega
  rw [Tab.wt, Finset.sum_congr rfl key,
    Finset.sum_range (fun i => (∑ j ∈ Finset.range m, extM A i j) • Finsupp.single (y i) 1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_range (fun j => extM A i j), Finset.sum_smul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [extM]

/-- **RSK preserves weights**: the contents of `P` and `Q` are the column and row sums. -/
theorem wt_rskEquiv {ι : Type*} (x y : ℕ → ι) (hm : m ≤ N) (A : Fin n → Fin m → ℕ) :
    (rskEquiv hm A).wt x y = matWt x y A := by
  show (rskFwd (N := N) A).wt x y = _
  rw [Pairs.wt, wt_fst x hm, wt_snd y hm, matWt, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_add]

/-- Pairs of tableaux of the same shape, sorted by shape. -/
def pairsSigma : Pairs N n m ≃
    Σ lam : Part, {T : Tab N m // T.shape = lam} × {T : Tab N n // T.shape = lam} where
  toFun pq := ⟨pq.1.1.shape, (⟨pq.1.1, rfl⟩, ⟨pq.1.2, pq.2.symm⟩)⟩
  invFun s := ⟨(s.2.1.1, s.2.2.1), s.2.1.2.trans s.2.2.2.symm⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨lam, ⟨P, hP⟩, ⟨Q, hQ⟩⟩
    subst hP
    rfl

/-! ## The Cauchy identity -/

section Cauchy

variable {ι R : Type*} [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
  [T3Space R]

omit [IsTopologicalSemiring R] [T3Space R] in
/-- The matrices form a valued set: their total weight is summable. -/
theorem summable_matWt (x y : ℕ → ι) :
    Summable (fun A : Fin n → Fin m → ℕ => (mono (matWt x y A) : MvPowerSeries ι R)) :=
  summable_mono (finiteFibres_matWt x y)

omit [IsTopologicalSemiring R] [T3Space R] in
theorem summable_pairs (x y : ℕ → ι) (hm : m ≤ N) :
    Summable (fun pq : Pairs N n m => (mono (pq.wt x y) : MvPowerSeries ι R)) := by
  rw [← (rskEquiv hm).summable_iff]
  convert summable_matWt (R := R) (n := n) (m := m) x y using 1
  funext A
  simp only [Function.comp_apply, wt_rskEquiv]

omit [IsTopologicalSemiring R] [T3Space R] in
theorem schur_mul_schur (x y : ℕ → ι) (lam : Part) :
    schur R x N m lam * schur R y N n lam
      = ∑' c : {T : Tab N m // T.shape = lam} × {T : Tab N n // T.shape = lam},
          (mono (Pairs.wt x y (pairsSigma.symm ⟨lam, c⟩)) : MvPowerSeries ι R) := by
  have := Fintype.ofFinite {T : Tab N m // T.shape = lam}
  have := Fintype.ofFinite {T : Tab N n // T.shape = lam}
  rw [schur, schur, tsum_fintype, tsum_fintype, tsum_fintype, Finset.sum_mul_sum,
    ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [monomial_mul_monomial, one_mul]
  rfl

/-- **The Cauchy identity**, in `m` variables `x` and `n` variables `y`, as an identity of
total weights in `MvPowerSeries ι R` with the product topology:

  `∑' λ, s_λ(x₀, …, x_{m−1}) s_λ(y₀, …, y_{n−1}) = ∑' A, ∏_{i<n, j<m} (x_j y_i) ^ (A i j)`,

the sum on the right over all `ℕ`-matrices with `n` rows and `m` columns. Shapes are padded to
`N ≥ m` rows. Proved by transporting weights along `rskEquiv`. -/
theorem cauchy (x y : ℕ → ι) (hm : m ≤ N) :
    ∑' lam : Part, schur R x N m lam * schur R y N n lam
      = ∑' A : Fin n → Fin m → ℕ, (mono (matWt x y A) : MvPowerSeries ι R) := by
  have : T3Space (MvPowerSeries ι R) := inferInstanceAs (T3Space ((ι →₀ ℕ) → R))
  have h1 : ∑' A : Fin n → Fin m → ℕ, (mono (matWt x y A) : MvPowerSeries ι R)
      = ∑' pq : Pairs N n m, (mono (pq.wt x y) : MvPowerSeries ι R) := by
    rw [← (rskEquiv hm).tsum_eq]
    simp only [wt_rskEquiv]
  let F : Pairs N n m → MvPowerSeries ι R := fun pq => mono (pq.wt x y)
  have hs : Summable (F ∘ (pairsSigma (N := N) (n := n) (m := m)).symm) :=
    (pairsSigma (N := N) (n := n) (m := m)).symm.summable_iff.mpr (summable_pairs x y hm)
  rw [h1, ← (pairsSigma (N := N) (n := n) (m := m)).symm.tsum_eq F]
  refine Eq.trans ?_ (Summable.tsum_sigma' (fun _ => Summable.of_finite) hs).symm
  exact tsum_congr (fun lam => schur_mul_schur x y lam)

/-- The family `λ ↦ s_λ(x) s_λ(y)` is summable. -/
theorem summable_schur_mul_schur (x y : ℕ → ι) (hm : m ≤ N) :
    Summable (fun lam : Part => schur R x N m lam * schur R y N n lam) := by
  have : T3Space (MvPowerSeries ι R) := inferInstanceAs (T3Space ((ι →₀ ℕ) → R))
  have := Summable.sigma' ((pairsSigma (N := N) (n := n) (m := m)).symm.summable_iff.mpr
    (summable_pairs (R := R) x y hm)) (fun _ => Summable.of_finite)
  convert this using 1
  funext lam
  exact schur_mul_schur x y lam

end Cauchy

section Product

variable {ι R : Type*} [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
  [T3Space R]

/-- The weight of the cell `(i, j)`: `x_j + y_i`. -/
noncomputable def cellWt {ι : Type*} (x y : ℕ → ι) (i j : ℕ) : ι →₀ ℕ :=
  Finsupp.single (x j) 1 + Finsupp.single (y i) 1

theorem cellWt_ne_zero {ι : Type*} (x y : ℕ → ι) (i j : ℕ) : cellWt x y i j ≠ 0 := by
  intro h
  have := congrArg (fun f => f (x j)) h
  simp [cellWt] at this

/-- **The matrices as a product of geometric series**:
`Σ' A, ∏ (x_j y_i) ^ (A i j) = ∏_{i<n, j<m} Σ' t, (x_j y_i) ^ t`. -/
theorem tsum_matWt_eq_prod (x y : ℕ → ι) :
    ∑' A : Fin n → Fin m → ℕ, (mono (matWt x y A) : MvPowerSeries ι R)
      = ∏ i : Fin n, ∏ j : Fin m, ∑' t : ℕ, (mono (t • cellWt x y i j) : MvPowerSeries ι R) := by
  obtain ⟨-, h⟩ := tsum_mono_pi (R := R) (fun p : Fin n × Fin m => cellWt x y p.1 p.2)
    (fun p => cellWt_ne_zero x y p.1 p.2)
  let E : (Fin n → Fin m → ℕ) ≃ (Fin n × Fin m → ℕ) := (Equiv.curry _ _ _).symm
  have hw : ∀ A, matWt x y A = ∑ p, (E A) p • cellWt x y p.1 p.2 := by
    intro A
    rw [matWt, Fintype.sum_prod_type]
    rfl
  calc ∑' A : Fin n → Fin m → ℕ, (mono (matWt x y A) : MvPowerSeries ι R)
      = ∑' A : Fin n → Fin m → ℕ,
          (mono (∑ p, (E A) p • cellWt x y p.1 p.2) : MvPowerSeries ι R) := by simp only [hw]
    _ = _ := (E.tsum_eq (fun B => (mono (∑ p, B p • cellWt x y p.1 p.2) :
          MvPowerSeries ι R))).trans h
    _ = _ := Fintype.prod_prod_type _

end Product

/-- **The Cauchy identity, product form**: in `MvPowerSeries ι R` with the product topology,

  `(∏_{i<n, j<m} (1 − x_j y_i)) · Σ' λ, s_λ(x₀, …, x_{m−1}) s_λ(y₀, …, y_{n−1}) = 1`,

for shapes padded to `N ≥ m` rows. -/
theorem cauchy_prod {ι R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T3Space R] (x y : ℕ → ι) (hm : m ≤ N) :
    (∏ i : Fin n, ∏ j : Fin m, (1 - X (x j) * X (y i) : MvPowerSeries ι R))
      * ∑' lam : Part, schur R x N m lam * schur R y N n lam = 1 := by
  rw [cauchy x y hm, tsum_matWt_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun i _ => ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun j _ => ?_)
  have : (X (x j) * X (y i) : MvPowerSeries ι R) = mono (cellWt x y i j) := by
    rw [X, X, monomial_mul_monomial, one_mul]
    rfl
  rw [this]
  exact one_sub_mul_tsum_mono_smul (cellWt_ne_zero x y i j)

end RMT.Symmetric
