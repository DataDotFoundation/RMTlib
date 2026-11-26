import RMTlib.Symmetric.Bialternant
import MeaningLib.Frame.Pattern

/-!
# Dual Jacobi–Trudi

For values `a : ℕ → R` in a commutative ring and a partition `λ : Fin N → ℕ` inside the
`N × K` box, with conjugate `λ' = conjV K λ` (`λ'_j = #{i | j < λ_i}`, `K` rows),

  `s_{λ'}(a₀, …, a_{m−1}) = det (e_{λ_i − i + j}(a₀, …, a_{m−1}))_{i, j < N}`

(`schurV_conjV_eq_eDet`; column form `schurV_eq_eDet_conjV`). With `schurV_eq_det` (the
`h`-determinant) this gives both halves of Jacobi–Trudi for the tableau Schur polynomials
`schurV`, over any commutative ring.

## Proof: branching over vertical strips

The proof mirrors RMTlib's Jacobi–Trudi (`schurV_eq_det`), boson ↔ fermion. There the
`h`-determinant branches in the last variable over **horizontal** strips (Cauchy–Binet). Here
`e_k(a₀, …, a_m) = e_k(a₀, …, a_{m−1}) + a_m e_{k−1}(a₀, …, a_{m−1})` (`eZ_succ`) makes each row
a sum of two rows, and multilinearity branches the `e`-determinant over the sets `J` of rows
that lose a box (`eDet_succ`). Only the **vertical** strips survive
(`eDet_eq_zero_of_not_isVStrip`: otherwise two rows coincide or the last row vanishes), and a
vertical strip of `λ` is a horizontal strip of `λ'` (`gtStep_conjV_iff`, `sum_interl_conjV`), so
the branching rule of `schurV` on `λ'` (`schurV_succ`) closes the induction.

## Main results

* `eZ`, `eZ_succ`: the elementary symbols on `ℤ` and their branching.
* `eDet`, `eDet_succ`, `eDet_eq_zero_of_not_isVStrip`: the dual Jacobi–Trudi determinant and its
  branching over vertical strips.
* `conjV`, `lt_conjV_iff`, `conjV_conjV`, `sum_conjV`, `gtStep_conjV_iff`, `sum_interl_conjV`:
  conjugation of partitions in a box.
* `schurV_conjV_eq_eDet`, `schurV_eq_eDet_conjV`: dual Jacobi–Trudi.
-/

open Finset Matrix

namespace RMT.Symmetric

variable {R : Type*} [CommRing R] {N K : ℕ}

/-! ## The elementary symbols -/

/-- The elementary symmetric polynomial `e_k(a₀, …, a_{n−1})` as a symbol indexed by `k ∈ ℤ`,
`0` for `k < 0`. -/
noncomputable def eZ (a : ℕ → R) (n : ℕ) (k : ℤ) : R := if 0 ≤ k then eV a n k.toNat else 0

theorem eZ_neg (a : ℕ → R) (n : ℕ) {k : ℤ} (hk : k < 0) : eZ a n k = 0 := by
  simp [eZ, not_le.mpr hk]

@[simp] theorem eZ_natCast (a : ℕ → R) (n k : ℕ) : eZ a n k = eV a n k := by
  simp [eZ]

/-- `e_k` over the variables indexed by `range n`. -/
theorem eV_eq_sum_range (a : ℕ → R) (n k : ℕ) :
    eV a n k = ∑ S ∈ (range n).powersetCard k, ∏ i ∈ S, a i := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, powersetCard_map, sum_map, eV]
  refine sum_congr rfl fun S _ => ?_
  simp [Finset.mapEmbedding]

/-- `e_0 = 1`. -/
@[simp] theorem eV_zero_index (a : ℕ → R) (n : ℕ) : eV a n 0 = 1 := by
  simp [eV]

/-- `e_k = 0` for `k > n`. -/
theorem eV_eq_zero_of_lt (a : ℕ → R) {n k : ℕ} (h : n < k) : eV a n k = 0 := by
  rw [eV, powersetCard_eq_empty.mpr (by simpa using h), sum_empty]

/-- **Adding a variable**: `e_{k+1}(a₀, …, a_n) = e_{k+1}(a₀, …, a_{n−1}) + a_n e_k(a₀, …, a_{n−1})`. -/
theorem eV_succ_succ (a : ℕ → R) (n k : ℕ) :
    eV a (n + 1) (k + 1) = eV a n (k + 1) + a n * eV a n k := by
  classical
  have hn : n ∉ range n := by simp
  rw [eV_eq_sum_range, eV_eq_sum_range, eV_eq_sum_range, range_add_one,
    powersetCard_succ_insert hn, sum_union, sum_image, mul_sum]
  · congr 1
    refine sum_congr rfl fun S hS => ?_
    rw [prod_insert fun h => hn ((mem_powersetCard.mp hS).1 h)]
  · intro S hS T hT h
    have hS' : n ∉ S := fun h => hn ((mem_powersetCard.mp hS).1 h)
    have hT' : n ∉ T := fun h => hn ((mem_powersetCard.mp hT).1 h)
    rw [← erase_insert hS', ← erase_insert hT']
    exact congrArg (·.erase n) h
  · rw [disjoint_left]
    intro S hS hS'
    obtain ⟨T, _, rfl⟩ := mem_image.mp hS'
    exact hn ((mem_powersetCard.mp hS).1 (mem_insert_self n T))

/-- **The fermionic branching of the symbol**: `e_k(a₀, …, a_n) = e_k(a₀, …, a_{n−1}) +
a_n e_{k−1}(a₀, …, a_{n−1})`, for every `k ∈ ℤ`. -/
theorem eZ_succ (a : ℕ → R) (n : ℕ) (k : ℤ) :
    eZ a (n + 1) k = eZ a n k + a n * eZ a n (k - 1) := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [eZ_neg a _ hk, eZ_neg a _ hk, eZ_neg a _ (by omega)]; ring
  · rw [eZ_neg a n (by omega : (0 : ℤ) - 1 < 0)]
    simp [eZ]
  · obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = ((k' + 1 : ℕ) : ℤ) := ⟨k.toNat - 1, by omega⟩
    rw [eZ_natCast, eZ_natCast, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring,
      eZ_natCast, eV_succ_succ]

/-- With no variables, `e_k = [k = 0] = h_k`. -/
theorem eZ_zero_eq_hE (a : ℕ → R) : eZ a 0 = hE a 0 := by
  funext k
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [eZ_neg a 0 hk, hE_neg a 0 hk]
  · simp [eZ, hE]
  · obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = ((k' + 1 : ℕ) : ℤ) := ⟨k.toNat - 1, by omega⟩
    rw [eZ_natCast, eV_eq_zero_of_lt a (by omega)]
    simp only [hE]
    rw [ite_eq_right (by omega)]

/-- `e_k(a₀, …, a_{n−1}) = 0` for `k > n`. -/
theorem eZ_eq_zero_of_lt (a : ℕ → R) {n : ℕ} {k : ℤ} (h : (n : ℤ) < k) : eZ a n k = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = (k' : ℤ) := ⟨k.toNat, by omega⟩
  rw [eZ_natCast, eV_eq_zero_of_lt a (by omega)]

/-! ## The dual Jacobi–Trudi determinant and its branching -/

/-- **The dual Jacobi–Trudi determinant** `det (e_{x_i − i + j}(a₀, …, a_{m−1}))_{i, j < N}`, on
integer vectors `x` (so that removing a vertical strip never leaves the type). -/
noncomputable def eDet (a : ℕ → R) (m : ℕ) (x : Fin N → ℤ) : R :=
  det (of fun i j : Fin N => eZ a m (x i - i + j))

/-- The integer indicator `1_J`. -/
def indZ (J : Finset (Fin N)) : Fin N → ℤ := fun i => if i ∈ J then 1 else 0

/-- **Branching of the dual Jacobi–Trudi determinant**: with `t = a_m`, every row is the sum of
two rows (`eZ_succ`), and multilinearity expands the determinant over the sets `J` of rows that
lose a box: `det e(a₀, …, a_m)_x = Σ_J t^{|J|} det e(a₀, …, a_{m−1})_{x − 1_J}`. -/
theorem eDet_succ (a : ℕ → R) (m : ℕ) (x : Fin N → ℤ) :
    eDet a (m + 1) x = ∑ J : Finset (Fin N), a m ^ J.card * eDet a m (x - indZ J) := by
  classical
  let A : Fin N → Fin N → R := fun i j => eZ a m (x i - i + j)
  let B : Fin N → Fin N → R := fun i j => a m * eZ a m (x i - 1 - i + j)
  have hM : (of fun i j : Fin N => eZ a (m + 1) (x i - i + j)) = B + A := by
    ext i j
    simp only [of_apply, eZ_succ, A, B, Pi.add_apply]
    rw [add_comm]
    congr 3
    ring
  rw [eDet, hM]
  change detRowAlternating (B + A) = _
  rw [AlternatingMap.map_add_univ]
  refine sum_congr rfl fun J _ => ?_
  have hpw : (J.piecewise B A : Matrix (Fin N) (Fin N) R) = of fun i j : Fin N =>
      (if i ∈ J then a m else 1) * eZ a m ((x - indZ J) i - (i : ℕ) + (j : ℕ)) := by
    ext i j
    by_cases hi : i ∈ J <;> simp [Finset.piecewise, hi, A, B, indZ]
  change det (J.piecewise B A : Matrix (Fin N) (Fin N) R) = _
  have h := det_mul_column (fun i : Fin N => if i ∈ J then a m else 1)
    (of fun i j : Fin N => eZ a m ((x - indZ J) i - (i : ℕ) + (j : ℕ)))
  simp only [of_apply] at h
  rw [hpw, h, prod_ite_mem, univ_inter, prod_const]
  rfl

/-! ## Vertical strips -/

/-- `λ − 1_J`, on natural numbers. -/
def vsub (lam : Fin N → ℕ) (J : Finset (Fin N)) : Fin N → ℕ :=
  fun i => lam i - if i ∈ J then 1 else 0

/-- **`J` removes a vertical strip from `λ`**: every row of `J` has a box to lose, and what is
left is a partition. -/
def IsVStrip (lam : Fin N → ℕ) (J : Finset (Fin N)) : Prop :=
  (∀ i ∈ J, 0 < lam i) ∧ Antitone (vsub lam J)

/-- On a vertical strip, `λ − 1_J` is the integer difference. -/
theorem cast_vsub {lam : Fin N → ℕ} {J : Finset (Fin N)} (h : ∀ i ∈ J, 0 < lam i) :
    (fun i => ((vsub lam J i : ℕ) : ℤ)) = (fun i => (lam i : ℤ)) - indZ J := by
  funext i
  have := h i
  by_cases hi : i ∈ J <;> simp [vsub, indZ, hi] at this ⊢
  omega

/-- Removing a vertical strip removes `|J|` boxes. -/
theorem sum_vsub_add_card {lam : Fin N → ℕ} {J : Finset (Fin N)} (h : ∀ i ∈ J, 0 < lam i) :
    ∑ i, vsub lam J i + J.card = ∑ i, lam i := by
  classical
  have hJ : (J.card : ℕ) = ∑ i, if i ∈ J then 1 else 0 := by
    rw [sum_boole, Nat.cast_id, filter_mem_eq_inter, univ_inter]
  rw [hJ, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have := h i
  by_cases hi : i ∈ J <;> simp [vsub, hi] at this ⊢
  omega

/-- **Only vertical strips survive.** If `J` does not remove a vertical strip from the partition
`λ`, the determinant `det e_{λ − 1_J}` has two equal rows (`i ∈ J`, `i + 1 ∉ J`,
`λ_i = λ_{i+1}`) or a zero last row (`λ_{N−1} = 0` lowered to `−1`). -/
theorem eDet_eq_zero_of_not_isVStrip (a : ℕ → R) (m : ℕ) {lam : Fin N → ℕ} (hl : Antitone lam)
    {J : Finset (Fin N)} (hJ : ¬ IsVStrip lam J) :
    eDet a m ((fun i => (lam i : ℤ)) - indZ J) = 0 := by
  have key : (∃ i i' : Fin N, (i' : ℕ) = i + 1 ∧ i ∈ J ∧ i' ∉ J ∧ lam i = lam i') ∨
      (∃ i : Fin N, (i : ℕ) + 1 = N ∧ i ∈ J ∧ lam i = 0) := by
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    apply hJ
    have hpos : ∀ i ∈ J, 0 < lam i := by
      intro i hi
      by_contra h0
      classical
      let S := univ.filter fun i' => i ≤ i' ∧ i' ∈ J ∧ lam i' = 0
      have hS : S.Nonempty :=
        ⟨i, by simp only [S, mem_filter, mem_univ, true_and]; exact ⟨le_rfl, hi, by omega⟩⟩
      obtain ⟨k, hkS, hkmax⟩ : ∃ k ∈ S, ∀ k' ∈ S, k' ≤ k :=
        ⟨S.max' hS, S.max'_mem hS, fun k' h => S.le_max' k' h⟩
      have hi' := (mem_filter.mp hkS).2
      by_cases hN : (k : ℕ) + 1 = N
      · exact h2 _ hN hi'.2.1 hi'.2.2
      · let i'' : Fin N := ⟨k + 1, by omega⟩
        have hle : k ≤ i'' := by rw [Fin.le_def]; show (k : ℕ) ≤ k + 1; omega
        have hl0 : lam i'' = 0 := by have := hl hle; omega
        refine h1 k i'' rfl hi'.2.1 (fun hJ'' => ?_) (by omega)
        have := hkmax i'' (by simp only [S, mem_filter, mem_univ, true_and]
                              exact ⟨hi'.1.trans hle, hJ'', hl0⟩)
        rw [Fin.le_def] at this
        change (k : ℕ) + 1 ≤ k at this
        omega
    refine ⟨hpos, ?_⟩
    obtain _ | n := N
    · exact fun i => i.elim0
    · rw [Fin.antitone_iff_succ_le]
      intro i
      have h := hl (Fin.castSucc_le_succ i)
      have hp1 := hpos i.castSucc
      have hp2 := hpos i.succ
      have hb := h1 i.castSucc i.succ (by simp)
      simp only [vsub] at h hb ⊢
      by_cases hc : i.castSucc ∈ J <;> by_cases hs : i.succ ∈ J <;> simp [hc, hs] at hp1 hp2 hb ⊢ <;>
        omega
  rcases key with ⟨i, i', hii', hi, hi', heq⟩ | ⟨i, hN, hi, h0⟩
  · refine det_zero_of_row_eq (i := i) (j := i') (fun h => by rw [h] at hii'; omega) ?_
    funext j
    simp only [of_apply, Pi.sub_apply, indZ, hi, hi', ite_true, ite_false, heq]
    congr 1
    omega
  · refine det_eq_zero_of_row_eq_zero i fun j => ?_
    simp only [of_apply, Pi.sub_apply, indZ, hi, ite_true, h0]
    exact eZ_neg a m (by have := j.2; push_cast; omega)

/-! ## The conjugate partition -/

/-- **The conjugate** `λ'_j = #{i | j < λ_i}` of `λ : Fin N → ℕ`, as a vector with `K` entries. -/
def conjV (K : ℕ) (lam : Fin N → ℕ) : Fin K → ℕ := fun j => #{i | (j : ℕ) < lam i}

/-- **The Galois connection of conjugation**: for a partition `λ`, the cell `(i, j)` is in `λ`
iff `(j, i)` is in `λ'`. -/
theorem lt_conjV_iff {lam : Fin N → ℕ} (hl : Antitone lam) (i : Fin N) (j : Fin K) :
    (i : ℕ) < conjV K lam j ↔ (j : ℕ) < lam i := by
  classical
  constructor
  · intro h
    by_contra hc
    have hsub : ({i' | (j : ℕ) < lam i'} : Finset (Fin N)) ⊆ Iio i := by
      intro i' hi'
      simp only [mem_filter, mem_univ, true_and] at hi'
      simp only [mem_Iio]
      by_contra hii
      have := hl (not_lt.mp hii)
      omega
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    exact absurd h (by simp only [conjV]; omega)
  · intro h
    have hsub : Iic i ⊆ ({i' | (j : ℕ) < lam i'} : Finset (Fin N)) := by
      intro i' hi'
      simp only [mem_filter, mem_univ, true_and]
      have := hl (mem_Iic.mp hi')
      omega
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    simp only [conjV]
    omega

/-- `λ'_j ≤ N`. -/
theorem conjV_le (lam : Fin N → ℕ) (j : Fin K) : conjV K lam j ≤ N :=
  (card_filter_le _ _).trans (by simp)

/-- The conjugate is a partition. -/
theorem antitone_conjV (lam : Fin N → ℕ) : Antitone (conjV K lam) := by
  intro j j' h
  refine card_le_card fun i hi => ?_
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  have : (j : ℕ) ≤ j' := h
  omega

/-- `#{j < K | j < c} = c` for `c ≤ K`. -/
theorem card_fin_lt {c : ℕ} (hc : c ≤ K) : #{j : Fin K | (j : ℕ) < c} = c := by
  classical
  have : ({j : Fin K | (j : ℕ) < c} : Finset (Fin K)).map Fin.valEmbedding = range c := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, by omega⟩, hx, rfl⟩⟩
  rw [← card_map, this, card_range]

/-- **Conjugation is an involution** on partitions inside the `N × K` box. -/
theorem conjV_conjV {lam : Fin N → ℕ} (hl : Antitone lam) (hK : ∀ i, lam i ≤ K) :
    conjV N (conjV K lam) = lam := by
  funext i
  have h : ∀ j : Fin K, (i : ℕ) < conjV K lam j ↔ (j : ℕ) < lam i := lt_conjV_iff hl i
  simp only [conjV] at h ⊢
  simp only [h]
  exact card_fin_lt (hK i)

/-- **Conjugation preserves size** inside the box. -/
theorem sum_conjV {lam : Fin N → ℕ} (hK : ∀ i, lam i ≤ K) :
    ∑ j, conjV K lam j = ∑ i, lam i := by
  classical
  simp only [conjV, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← card_filter, card_fin_lt (hK i)]

/-- Only the empty shape has the empty conjugate. -/
theorem conjV_eq_zero_iff {lam : Fin N → ℕ} (hl : Antitone lam) (hK : ∀ i, lam i ≤ K) :
    conjV K lam = 0 ↔ lam = 0 := by
  constructor
  · intro h
    rw [← conjV_conjV hl hK, h]
    funext i
    simp [conjV]
  · rintro rfl
    funext j
    simp [conjV]

/-- `a ≤ b` for `a ≤ N`, tested on `Fin N`. -/
theorem le_iff_forall_fin {a b : ℕ} (ha : a ≤ N) :
    a ≤ b ↔ ∀ i : Fin N, (i : ℕ) < a → (i : ℕ) < b := by
  constructor
  · intro h i hi; omega
  · intro h
    by_contra hc
    have := h ⟨b, by omega⟩ (by simp; omega)
    simp at this

/-- **A horizontal strip of `λ'` is a vertical strip of `λ`**: `ν'` interlaces `λ'` iff
`ν_i ≤ λ_i ≤ ν_i + 1` for every row. -/
theorem gtStep_conjV_iff {lam nu : Fin N → ℕ} (hl : Antitone lam) (hn : Antitone nu)
    (hlK : ∀ i, lam i ≤ K) (hnK : ∀ i, nu i ≤ K) :
    Weyl.GTStep (conjV K lam) (conjV K nu) ↔ ∀ i, nu i ≤ lam i ∧ lam i ≤ nu i + 1 := by
  constructor
  · rintro ⟨h1, h2⟩ i
    constructor
    · by_contra hc
      have hj : lam i < K := by have := hnK i; omega
      have := (le_iff_forall_fin (conjV_le nu ⟨lam i, hj⟩)).mp (h2 ⟨lam i, hj⟩) i
      rw [lt_conjV_iff hn, lt_conjV_iff hl] at this
      exact absurd (this (by simp; omega)) (by simp)
    · by_contra hc
      have hj : nu i + 1 < K := by have := hlK i; omega
      have := (le_iff_forall_fin (conjV_le lam ⟨nu i + 1, hj⟩)).mp
        (h1 ⟨nu i, by omega⟩ ⟨nu i + 1, hj⟩ rfl) i
      rw [lt_conjV_iff hl, lt_conjV_iff hn] at this
      exact absurd (this (by simp; omega)) (by simp)
  · intro h
    refine ⟨fun l j hj => (le_iff_forall_fin (conjV_le lam j)).mpr fun i hi => ?_,
      fun t => (le_iff_forall_fin (conjV_le nu t)).mpr fun i hi => ?_⟩
    · rw [lt_conjV_iff hl] at hi
      rw [lt_conjV_iff hn]
      have := h i
      omega
    · rw [lt_conjV_iff hn] at hi
      rw [lt_conjV_iff hl]
      have := h i
      omega

/-- If `ν ≤ λ ≤ ν + 1` row by row, `ν` is `λ` minus the rows where they differ. -/
theorem vsub_filter_lt {lam nu : Fin N → ℕ} (h : ∀ i, nu i ≤ lam i ∧ lam i ≤ nu i + 1) :
    vsub lam (univ.filter fun i => nu i < lam i) = nu := by
  funext i
  have := h i
  simp only [vsub, mem_filter, mem_univ, true_and]
  split_ifs <;> omega

open Classical in
/-- **Vertical strips of `λ` are horizontal strips of `λ'`**: the shapes `μ` interlacing `λ'` are
the conjugates `(λ − 1_J)'` of the vertical strips `J` of `λ`, each once. -/
theorem sum_interl_conjV {lam : Fin N → ℕ} (hl : Antitone lam) (hK : ∀ i, lam i ≤ K)
    (F : (Fin K → ℕ) → R) :
    ∑ mu ∈ interl (conjV K lam), F mu =
      ∑ J ∈ univ.filter (IsVStrip lam), F (conjV K (vsub lam J)) := by
  have hvK : ∀ J, ∀ i, vsub lam J i ≤ K := fun J i => (Nat.sub_le _ _).trans (hK i)
  have hstep : ∀ J, ∀ i, vsub lam J i ≤ lam i ∧ lam i ≤ vsub lam J i + 1 := by
    intro J i; simp only [vsub]; split_ifs <;> omega
  have hinv : ∀ mu ∈ interl (conjV K lam), conjV K (conjV N mu) = mu ∧
      ∀ i, conjV N mu i ≤ lam i ∧ lam i ≤ conjV N mu i + 1 := by
    intro mu hmu
    have hg := mem_interl.mp hmu
    have hma : Antitone mu := antitone_of_gtStep (antitone_conjV lam) hg
    have hmN : ∀ j, mu j ≤ N := fun j => (hg.2 j).trans (conjV_le lam j)
    have hc : conjV K (conjV N mu) = mu := conjV_conjV hma hmN
    rw [← hc] at hg
    exact ⟨hc, (gtStep_conjV_iff hl (antitone_conjV mu) hK (conjV_le mu)).mp hg⟩
  symm
  refine sum_nbij' (fun J => conjV K (vsub lam J))
    (fun mu => univ.filter fun i => conjV N mu i < lam i) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro J hJ
    have hJ : IsVStrip lam J := by simpa using hJ
    exact mem_interl.mpr ((gtStep_conjV_iff hl hJ.2 hK (hvK J)).mpr (hstep J))
  · intro mu hmu
    obtain ⟨_, h⟩ := hinv mu hmu
    rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hi; omega
    · rw [vsub_filter_lt h]; exact antitone_conjV mu
  · intro J hJ
    have hJ : IsVStrip lam J := by simpa using hJ
    simp only [conjV_conjV hJ.2 (hvK J)]
    ext i
    have := hJ.1 i
    by_cases hi : i ∈ J <;> simp [vsub, hi] at this ⊢
    omega
  · intro mu hmu
    obtain ⟨hc, h⟩ := hinv mu hmu
    simp only [vsub_filter_lt h, hc]

/-- **Dual Jacobi–Trudi**: for a partition `λ : Fin N → ℕ` inside the `N × K` box, the Schur
polynomial of the conjugate `λ'` (`K` rows) is the `e`-determinant of `λ`,

  `s_{λ'}(a₀, …, a_{m−1}) = det (e_{λ_i − i + j}(a₀, …, a_{m−1}))_{i, j < N}`,

over any commutative ring. Both sides branch in the last variable: the tableaux of `λ'` over
horizontal strips of `λ'` (`schurV_succ`), the determinant over vertical strips of `λ`
(`eDet_succ`, `eDet_eq_zero_of_not_isVStrip`), and the two are the same strips
(`sum_interl_conjV`). -/
@[frame_pattern]
theorem schurV_conjV_eq_eDet (a : ℕ → R) : ∀ (m : ℕ) (lam : Fin N → ℕ), Antitone lam →
    (∀ i, lam i ≤ K) → schurV a K m (conjV K lam) = eDet a m (fun i => (lam i : ℤ))
  | 0, lam, hl, hK => by
    rw [schurV_zero, eDet, eZ_zero_eq_hE,
      show (of fun i j : Fin N => hE a 0 ((lam i : ℤ) - i + j)) = jtMat a 0 lam from rfl,
      det_jtMat_zero a lam hl]
    simp only [conjV_eq_zero_iff hl hK]
  | m + 1, lam, hl, hK => by
    classical
    rw [schurV_succ, sum_interl_conjV hl hK, eDet_succ,
      ← sum_filter_add_sum_filter_not univ (IsVStrip lam),
      sum_eq_zero (s := univ.filter fun J => ¬ IsVStrip lam J) fun J hJ => by
        rw [eDet_eq_zero_of_not_isVStrip a m hl (mem_filter.mp hJ).2, mul_zero], add_zero]
    refine sum_congr rfl fun J hJ => ?_
    have hJ := (mem_filter.mp hJ).2
    have hvK : ∀ i, vsub lam J i ≤ K := fun i => (Nat.sub_le _ _).trans (hK i)
    rw [schurV_conjV_eq_eDet a m _ hJ.2 hvK, cast_vsub hJ.1, sum_conjV hK, sum_conjV hvK]
    congr 2
    have := sum_vsub_add_card hJ.1
    omega

/-- **Dual Jacobi–Trudi, column form**: for a partition `μ : Fin K → ℕ` with `μ_0 ≤ N`,
`s_μ = det (e_{μ'_i − i + j})_{i, j < N}`. -/
@[frame_pattern]
theorem schurV_eq_eDet_conjV (a : ℕ → R) (m : ℕ) {mu : Fin K → ℕ} (hm : Antitone mu)
    (hN : ∀ j, mu j ≤ N) :
    schurV a K m mu = eDet a m (fun i => (conjV N mu i : ℤ)) := by
  conv_lhs => rw [← conjV_conjV hm hN]
  exact schurV_conjV_eq_eDet a m _ (antitone_conjV mu) (conjV_le mu)

end RMT.Symmetric
