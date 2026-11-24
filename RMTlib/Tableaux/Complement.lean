import RMTlib.Tableaux.Exclusion

/-!
# Lemma 6 of Dehaye (arXiv:1201.4478): complementary partitions in the `k × k` square

`κ` and `λ` are *complementary* (`S_k(κ) = λ`) when the transpose of `λ` is the rotated
complement of `κ`: `λᵗ_j = k − κ_{k−1−j}`. Lemma 6 (after Macdonald, I.1) characterizes this by
the shifted sequences: `(κ_i + k − 1 − i)_i` and `(λ_i + k − 1 − i)_i` together list
`{0, …, 2k−1}` exactly once. The U(N) test (`toy_examples/scripts/un_test.py`) showed that Theorem 3 needs
exactly this transposed convention.

Both are proved here: `macdonald_1_7` (the shifted rows and shifted columns of one partition
partition `{0, …, 2k−1}`), and from it `lemma6`. The `#guard` at the end checks the equivalence
by enumeration for `k ≤ 4` as well.
-/

open Finset

namespace RMT

/-- `κ` and `λ` are complementary in the `k × k` square: `λᵗ_j = k − κ_{k−1−j}`. -/
def Complementary (k : ℕ) (kap lam : Fin k → ℕ) : Prop :=
  ∀ j : Fin k, tr lam j = k - kap ⟨k - 1 - j, by omega⟩

/-- The shifted sequences of `κ` and `λ` together list `{0, …, 2k−1}` exactly once. -/
def ShiftedPartition (k : ℕ) (kap lam : Fin k → ℕ) : Prop :=
  Disjoint (univ.image fun i : Fin k => kap i + (k - 1 - i)) (univ.image fun i : Fin k => lam i + (k - 1 - i)) ∧
  (univ.image fun i : Fin k => kap i + (k - 1 - i)) ∪ (univ.image fun i : Fin k => lam i + (k - 1 - i)) = range (2 * k)

instance (k : ℕ) (kap lam : Fin k → ℕ) : Decidable (Complementary k kap lam) := by
  unfold Complementary; infer_instance
instance (k : ℕ) (kap lam : Fin k → ℕ) : Decidable (ShiftedPartition k kap lam) := by
  unfold ShiftedPartition; infer_instance

/-- All partitions in the `k × k` box, as antitone functions `Fin k → ℕ`. -/
def boxPartitions (k : ℕ) : List (Fin k → ℕ) :=
  let rec go : ℕ → ℕ → List (List ℕ)
    | 0, _ => [[]]
    | r + 1, mx => (List.range (mx + 1)).flatMap fun p => (go r p).map (p :: ·)
  (go k k).map fun l => fun i => l.getD i.val 0

/-- The shifted row sequence `i ↦ κ_i + (k − 1 − i)`. -/
def rowSeq (k : ℕ) (kap : Fin k → ℕ) : Fin k → ℕ := fun i => kap i + (k - 1 - i)

/-- The shifted column sequence `j ↦ k + j − λᵗ_j`. -/
def colSeq (k : ℕ) (lam : Fin k → ℕ) : Fin k → ℕ := fun j => k + j - tr lam j

theorem colSeq_strictMono (k : ℕ) (lam : Fin k → ℕ) : StrictMono (colSeq k lam) := by
  intro j j' h
  have h1 := tr_antitone lam (j := j) (j' := j') (le_of_lt h)
  have h2 := tr_le lam j
  have h3 := tr_le lam j'
  have : (j : ℕ) < j' := h
  simp only [colSeq]
  omega

/-- **Macdonald (I.1.7)** in the `k × k` box: the shifted rows and the shifted columns of a
partition `λ` together list `{0, …, 2k−1}` exactly once. Classical (Macdonald, *Symmetric
functions and Hall polynomials*, I.1.7). -/
theorem macdonald_1_7 (k : ℕ) (lam : Fin k → ℕ) (hl : Antitone lam) (hlb : ∀ i, lam i ≤ k) :
    Disjoint (univ.image (rowSeq k lam)) (univ.image (colSeq k lam)) ∧
      univ.image (rowSeq k lam) ∪ univ.image (colSeq k lam) = range (2 * k) := by
  -- the shifted row of `i` and the shifted column of `j` never coincide
  have hne : ∀ i j : Fin k, rowSeq k lam i ≠ colSeq k lam j := by
    intro i j
    have hi := i.isLt
    have htj := tr_le lam j
    simp only [rowSeq, colSeq]
    by_cases hj : (j : ℕ) < lam i
    · -- the box `(i, j)` is in `λ`: rows `0..i` are longer than `j`
      have : i.val + 1 ≤ tr lam j := by
        unfold tr
        calc i.val + 1 = #(Iic i) := by rw [Fin.card_Iic]
          _ ≤ _ := card_le_card (by
              intro i' hi'
              simp only [mem_filter, mem_univ, true_and]
              exact lt_of_lt_of_le hj (hl (mem_Iic.mp hi')))
      omega
    · -- it is not: only rows `0..i-1` can be longer than `j`
      have : tr lam j ≤ i.val := by
        unfold tr
        calc #({i' : Fin k | (j : ℕ) < lam i'}) ≤ #(Iio i) := card_le_card (by
              intro i' hi'
              simp only [mem_filter, mem_univ, true_and] at hi'
              rw [mem_Iio]
              by_contra hge
              exact absurd (lt_of_lt_of_le hi' (hl (not_lt.mp hge))) (by omega))
          _ = i.val := by rw [Fin.card_Iio]
      omega
  have hdisj : Disjoint (univ.image (rowSeq k lam)) (univ.image (colSeq k lam)) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, rfl⟩ := mem_image.mp hx
    obtain ⟨j, -, hj⟩ := mem_image.mp hx'
    exact hne i j hj.symm
  refine ⟨hdisj, ?_⟩
  have hrow_inj : Function.Injective (rowSeq k lam) := by
    intro i i' h
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · have := hl hlt.le
      have hv : (i : ℕ) < i' := hlt
      have := i'.isLt
      simp only [rowSeq] at h
      omega
    · have := hl hlt.le
      have hv : (i' : ℕ) < i := hlt
      have := i.isLt
      simp only [rowSeq] at h
      omega
  have hsub : univ.image (rowSeq k lam) ∪ univ.image (colSeq k lam) ⊆ range (2 * k) := by
    intro x hx
    rw [mem_range]
    rcases mem_union.mp hx with h | h
    · obtain ⟨i, -, rfl⟩ := mem_image.mp h
      have := hlb i
      have := i.isLt
      simp only [rowSeq]
      omega
    · obtain ⟨j, -, rfl⟩ := mem_image.mp h
      have := j.isLt
      simp only [colSeq]
      omega
  refine eq_of_subset_of_card_le hsub ?_
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ hrow_inj,
    card_image_of_injective _ (colSeq_strictMono k lam).injective, card_univ, Fintype.card_fin,
    card_range]
  omega

theorem rowSeq_rev_strictMono (k : ℕ) (kap : Fin k → ℕ) (hk : Antitone kap) :
    StrictMono fun j : Fin k => rowSeq k kap (Fin.rev j) := by
  intro j j' h
  have hj : (j : ℕ) < j' := h
  have hrev : Fin.rev j' ≤ Fin.rev j := Fin.rev_le_rev.mpr h.le
  have hmono := hk hrev
  simp only [rowSeq, Fin.val_rev]
  have := j'.isLt
  omega

/-- If `A` and `C` are both complements of `B` in `R`, they are equal. -/
theorem eq_of_compl {A B C R : Finset ℕ} (h1 : Disjoint A B) (h2 : A ∪ B = R)
    (h3 : Disjoint C B) (h4 : C ∪ B = R) : A = C := by
  ext x
  constructor
  · intro hx
    have hR : x ∈ C ∪ B := h4 ▸ h2 ▸ mem_union_left _ hx
    rcases mem_union.mp hR with h | h
    · exact h
    · exact absurd h (disjoint_left.mp h1 hx)
  · intro hx
    have hR : x ∈ A ∪ B := h2 ▸ h4 ▸ mem_union_left _ hx
    rcases mem_union.mp hR with h | h
    · exact h
    · exact absurd h (disjoint_left.mp h3 hx)

/-- **Lemma 6** (Dehaye 1201.4478): complementarity in the `k × k` square is the shifted-sequence condition. -/
theorem lemma6 (k : ℕ) (kap lam : Fin k → ℕ) (hk : Antitone kap) (hl : Antitone lam)
    (hkb : ∀ i, kap i ≤ k) (hlb : ∀ i, lam i ≤ k) :
    Complementary k kap lam ↔ ShiftedPartition k kap lam := by
  obtain ⟨hd', hu'⟩ := macdonald_1_7 k lam hl hlb
  have hcol : ∀ j : Fin k, rowSeq k kap (Fin.rev j) = colSeq k lam j ↔
      tr lam j = k - kap ⟨k - 1 - j, by omega⟩ := by
    intro j
    have hrev : Fin.rev j = ⟨k - 1 - j, by omega⟩ := by ext; simp [Fin.val_rev]; omega
    have hb := hkb (Fin.rev j)
    have ht := tr_le lam j
    simp only [rowSeq, colSeq, Fin.val_rev]
    rw [hrev] at hb ⊢
    omega
  constructor
  · intro hC
    have hB : univ.image (colSeq k lam) = univ.image (rowSeq k kap) := by
      ext x
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨Fin.rev j, ((hcol j).mpr (hC j))⟩
      · rintro ⟨i, rfl⟩
        refine ⟨Fin.rev i, ?_⟩
        have := (hcol (Fin.rev i)).mpr (hC (Fin.rev i))
        rw [Fin.rev_rev] at this
        exact this.symm
    rw [hB] at hd' hu'
    exact ⟨hd'.symm, by rw [union_comm]; exact hu'⟩
  · rintro ⟨hd, hu⟩
    have hAC : univ.image (rowSeq k kap) = univ.image (colSeq k lam) :=
      eq_of_compl hd hu hd'.symm (by rw [union_comm]; exact hu')
    have hrange : Set.range (fun j : Fin k => rowSeq k kap (Fin.rev j)) = Set.range (colSeq k lam) := by
      have e1 : Set.range (fun j : Fin k => rowSeq k kap (Fin.rev j)) = Set.range (rowSeq k kap) :=
        Fin.rev_surjective.range_comp (rowSeq k kap)
      rw [e1, ← Set.image_univ, ← Set.image_univ, ← coe_univ, ← coe_image, ← coe_image, hAC]
    have hfun := ((rowSeq_rev_strictMono k kap hk).range_inj (colSeq_strictMono k lam)).mp hrange
    intro j
    exact (hcol j).mp (congrFun hfun j)

-- Evidence: the equivalence on every pair of partitions in the box, k ≤ 4.
#guard (List.range 5).all fun k =>
  (boxPartitions k).all fun kap => (boxPartitions k).all fun lam =>
    decide (Complementary k kap lam) == decide (ShiftedPartition k kap lam)

end RMT
