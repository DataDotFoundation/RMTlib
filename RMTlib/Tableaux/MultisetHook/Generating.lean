import RMTlib.Tableaux.MultisetHook.Corollary4
import RMTlib.Tableaux.MultisetHook.Littlewood

/-!
# The generating-function results, coefficient by coefficient

The paper's §4–5 are identities of `q`-series. Their combinatorial content is a statement about
the coefficient of each `qⁿ`, a finite sum over partitions of `n` (`diagrams n`). This file
proves that content:

* `hanJi_comb` (**Theorem 15, combinatorial form**): the Littlewood bijection is
  weight-preserving, so
  `∑_{|λ|=n} x^{#H_r(λ)} ∏_{h ∈ H_r(λ)} ρ(h)
     = ∑_{κ r-core, (λ^ρ)_ρ, |κ| + r∑|λ^ρ| = n} ∏_ρ x^{|λ^ρ|} ∏_{h ∈ H(λ^ρ)} ρ(rh)`.
  Han–Ji's identity (38) is this, read as an equality of generating functions.
* `lemma13_iff_macdonald` (**Lemma 13 ⇔ Macdonald's identity, specialised**): with
  `τ(k) = w^k − w^{−k}` (the paper's `sin(kz)`, `w = e^{iz}`, up to a constant), the weight
  `1 − sin²(tz)/sin²(hz)` is `τ(h − t)τ(h + t)/τ(h)²` (Lemma 12). For every sequence `c`,
  `∑_{|λ|=n, t-core} ∏_h τ(h−t)τ(h+t)/τ(h)² = c_n` for all `n` iff
  `∑_{|λ|=n, t-core} ∏_{i<j} τ(u_i − u_j) = (−1)^{(t−1)/2} ∏_k τ(k)^{t−k} c_n` for all `n`.
  This is the paper's step from Theorem 11 to Lemma 13 (`t` odd), via Corollary 4. With `c` the
  coefficients of the product in Eq. (35), the second statement is the specialisation of
  Macdonald's identity displayed before Lemma 12.
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

open Classical

/-! ### Partitions of `n` -/

/-- **The Young diagrams with `n` cells**, as a `Finset`. -/
def diagrams (n : ℕ) : Finset YoungDiagram :=
  ((range n ×ˢ range n).powerset.filter
    fun s : Finset (ℕ × ℕ) => IsLowerSet (↑s : Set (ℕ × ℕ)) ∧ s.card = n).attach.image
      fun s => ⟨s.1, (mem_filter.mp s.2).2.1⟩

theorem cells_subset_box {μ : YoungDiagram} : μ.cells ⊆ range μ.cells.card ×ˢ range μ.cells.card := by
  intro c hc
  have hrect : range (c.1 + 1) ×ˢ range (c.2 + 1) ⊆ μ.cells := by
    intro d hd
    simp only [mem_product, mem_range] at hd
    rw [YoungDiagram.mem_cells] at hc ⊢
    exact μ.up_left_mem (by omega) (by omega) hc
  have := card_le_card hrect
  rw [card_product, card_range, card_range] at this
  simp only [mem_product, mem_range]
  constructor <;> nlinarith

theorem mem_diagrams {n : ℕ} {μ : YoungDiagram} : μ ∈ diagrams n ↔ μ.cells.card = n := by
  constructor
  · intro h
    obtain ⟨⟨s, hs⟩, -, rfl⟩ := mem_image.mp h
    exact (mem_filter.mp hs).2.2
  · intro h
    have hs : μ.cells ∈ (range n ×ˢ range n).powerset.filter
        (fun s : Finset (ℕ × ℕ) => IsLowerSet (↑s : Set (ℕ × ℕ)) ∧ s.card = n) := by
      rw [mem_filter, mem_powerset]
      exact ⟨h ▸ cells_subset_box, μ.isLowerSet, h⟩
    exact mem_image.mpr ⟨⟨μ.cells, hs⟩, mem_attach _ _, rfl⟩

/-- The partitions of size at most `n`. -/
def diagramsLE (n : ℕ) : Finset YoungDiagram := (range (n + 1)).biUnion diagrams

theorem mem_diagramsLE {n : ℕ} {μ : YoungDiagram} : μ ∈ diagramsLE n ↔ μ.cells.card ≤ n := by
  simp only [diagramsLE, mem_biUnion, mem_range, mem_diagrams]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · intro h; exact ⟨_, by omega, rfl⟩

theorem card_hooks (μ : YoungDiagram) : (hooks μ).card = μ.cells.card := by
  simp [hooks]

/-! ### Theorem 15, combinatorial form -/

/-- The index set of the Littlewood decomposition in size `n`: an `r`-core `κ` and partitions
`(λ^ρ)_{ρ<r}` with `|κ| + r ∑ |λ^ρ| = n`. -/
def lwIndex (r n : ℕ) : Finset (YoungDiagram × (Fin r → YoungDiagram)) :=
  ((diagramsLE n).filter (IsTCore r) ×ˢ Fintype.piFinset fun _ => diagramsLE n).filter
    fun x => x.1.cells.card + r * ∑ ρ, (x.2 ρ).cells.card = n

/-- Extending a tuple by `⊥`. -/
def extTuple {r : ℕ} (q : Fin r → YoungDiagram) (ρ : ℕ) : YoungDiagram :=
  if h : ρ < r then q ⟨ρ, h⟩ else ⊥

/-- The partition with given `r`-core and `r`-quotient. -/
def lwBuild {r : ℕ} (hr : 0 < r) (x : YoungDiagram × (Fin r → YoungDiagram)) : YoungDiagram :=
  if h : IsTCore r x.1 then Classical.choose (littlewood hr x.1 h (extTuple x.2)).exists else ⊥

theorem lwBuild_spec {r : ℕ} (hr : 0 < r) {x : YoungDiagram × (Fin r → YoungDiagram)}
    (h : IsTCore r x.1) :
    core r (lwBuild hr x) = x.1 ∧ ∀ ρ < r, quot r (lwBuild hr x) ρ = extTuple x.2 ρ := by
  unfold lwBuild; rw [dif_pos h]
  exact Classical.choose_spec (littlewood hr x.1 h (extTuple x.2)).exists

theorem multiset_prod_sum {R : Type*} [CommMonoid R] {ι : Type*} (s : Finset ι)
    (m : ι → Multiset ℤ) (g : ℤ → R) :
    ((∑ i ∈ s, m i).map g).prod = ∏ i ∈ s, ((m i).map g).prod := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, Multiset.map_add, Multiset.prod_add, ih]

/-- **Dehaye–Han, Theorem 15 (Han–Ji), combinatorial form**: the Littlewood bijection carries
`x^{#H_r(λ)} ∏_{h ∈ H_r(λ)} ρ(h)` to `∏_ρ x^{|λ^ρ|} ∏_{h ∈ H(λ^ρ)} ρ(rh)`. -/
theorem hanJi_comb {r : ℕ} (hr : 0 < r) (n : ℕ) {R : Type*} [CommRing R] (x : R) (ρf : ℤ → R) :
    ∑ μ ∈ diagrams n, x ^ ((hooks μ).filter (fun h => (r : ℤ) ∣ h)).card *
        (((hooks μ).filter (fun h => (r : ℤ) ∣ h)).map ρf).prod =
      ∑ y ∈ lwIndex r n, ∏ ρ, x ^ (y.2 ρ).cells.card *
        ((hooks (y.2 ρ)).map fun h => ρf (r * h)).prod := by
  refine sum_bij' (fun μ _ => (core r μ, fun ρ : Fin r => quot r μ ρ)) (fun y _ => lwBuild hr y)
    ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    rw [mem_diagrams] at hμ
    have hsize := card_littlewood hr μ
    rw [← Fin.sum_univ_eq_sum_range (fun ρ => ((quot r μ ρ).cells.card : ℤ))] at hsize
    simp only [lwIndex, mem_filter, mem_product, Fintype.mem_piFinset, mem_diagramsLE]
    have hq : ∀ ρ : Fin r, (quot r μ ρ).cells.card ≤ n := fun ρ => by
      have := single_le_sum (f := fun ρ : Fin r => ((quot r μ ρ).cells.card : ℤ))
        (fun _ _ => by positivity) (mem_univ ρ)
      have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
      have : (0 : ℤ) ≤ (core r μ).cells.card := by positivity
      have : ((quot r μ ρ).cells.card : ℤ) ≤ n := by nlinarith
      exact_mod_cast this
    refine ⟨⟨⟨?_, core_isTCore hr μ⟩, hq⟩, ?_⟩
    · have : (0 : ℤ) ≤ r * ∑ ρ : Fin r, ((quot r μ ρ).cells.card : ℤ) := by positivity
      have : ((core r μ).cells.card : ℤ) ≤ n := by omega
      exact_mod_cast this
    · have := hsize; rw [hμ] at this; exact_mod_cast this.symm
  · rintro ⟨κ, q⟩ hy
    simp only [lwIndex, mem_filter, mem_product, Fintype.mem_piFinset, mem_diagramsLE] at hy
    obtain ⟨⟨⟨-, hκ⟩, -⟩, hn⟩ := hy
    obtain ⟨hc, hq⟩ := lwBuild_spec hr (x := (κ, q)) hκ
    rw [mem_diagrams]
    have hsize := card_littlewood hr (lwBuild hr (κ, q))
    rw [← Fin.sum_univ_eq_sum_range (fun ρ => ((quot r (lwBuild hr (κ, q)) ρ).cells.card : ℤ))]
      at hsize
    simp only [hc] at hsize
    have : ∀ ρ : Fin r, quot r (lwBuild hr (κ, q)) ρ = q ρ := fun ρ => by
      rw [hq ρ ρ.isLt, extTuple, dif_pos ρ.isLt]
    simp only [this] at hsize
    have : ((lwBuild hr (κ, q)).cells.card : ℤ) = n := by rw [hsize]; exact_mod_cast hn
    exact_mod_cast this
  · intro μ hμ
    have hκ := core_isTCore hr μ
    obtain ⟨hc, hq⟩ := lwBuild_spec hr (x := (core r μ, fun ρ : Fin r => quot r μ ρ)) hκ
    exact ((littlewood hr (core r μ) hκ (quot r μ)).unique ⟨hc, fun ρ hρ => by
      rw [hq ρ hρ, extTuple, dif_pos hρ]⟩ ⟨rfl, fun _ _ => rfl⟩)
  · rintro ⟨κ, q⟩ hy
    simp only [lwIndex, mem_filter, mem_product] at hy
    obtain ⟨⟨⟨-, hκ⟩, -⟩, -⟩ := hy
    obtain ⟨hc, hq⟩ := lwBuild_spec hr (x := (κ, q)) hκ
    simp only [Prod.mk.injEq]
    refine ⟨hc, funext fun ρ => ?_⟩
    rw [hq ρ ρ.isLt, extTuple, dif_pos ρ.isLt]
  · intro μ _
    rw [hooks_dvd hr μ, Multiset.card_sum, multiset_prod_sum, ← Fin.sum_univ_eq_sum_range
      (fun ρ => Multiset.card ((hooks (quot r μ ρ)).map ((r : ℤ) * ·))),
      ← Fin.prod_univ_eq_prod_range (fun ρ => (((hooks (quot r μ ρ)).map ((r : ℤ) * ·)).map ρf).prod),
      ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun ρ _ => ?_
    rw [Multiset.card_map, card_hooks, Multiset.map_map]
    rfl

/-! ### Lemma 13 ⇔ Macdonald's identity, specialised -/

/-- `τ(k) = w^k − w^{−k}`, the paper's `sin(kz)` (`w = e^{iz}`) up to the constant `2i`. -/
def tauW {F : Type*} [Field F] (w : F) (k : ℤ) : F := w ^ k - w ^ (-k)

variable {F : Type*} [Field F] {w : F}

theorem tauW_neg (w : F) (k : ℤ) : tauW w (-k) = -tauW w k := by
  simp only [tauW, neg_neg]; ring

/-- `τ` as a unit, for `w` with `w^k ≠ w^{−k}` (`k ≠ 0`); `1` at `0`. -/
def tauU (w : F) (hw : ∀ k : ℤ, k ≠ 0 → w ^ k ≠ w ^ (-k)) (k : ℤ) : Fˣ :=
  if h : k = 0 then 1 else Units.mk0 (tauW w k) (sub_ne_zero.mpr (hw k h))

theorem tauU_val (hw : ∀ k : ℤ, k ≠ 0 → w ^ k ≠ w ^ (-k)) {k : ℤ} (hk : k ≠ 0) :
    ((tauU w hw k : Fˣ) : F) = tauW w k := by
  rw [tauU, dif_neg hk]; rfl

theorem val_mprod (m : Multiset ℤ) (f : ℤ → Fˣ) :
    (((m.map f).prod : Fˣ) : F) = (m.map fun h => (f h : F)).prod := by
  rw [← Units.coeHom_apply, map_multiset_prod, Multiset.map_map]; rfl

theorem tauU_odd (hw : ∀ k : ℤ, k ≠ 0 → w ^ k ≠ w ^ (-k)) (k : ℤ) (hk : k ≠ 0) :
    tauU w hw (-k) = -1 * tauU w hw k := by
  ext
  rw [tauU_val hw (neg_ne_zero.mpr hk), Units.val_mul, tauU_val hw hk, tauW_neg]
  simp

/-- **Lemma 13 ⇔ Macdonald's identity (specialised)**: for `t = 2t' + 1` and any coefficients
`c`, the core sum of the hook weights is `c` iff the core sum of the Vandermonde product
`∏_{i<j} τ(u_i − u_j)` is `(−1)^{t'} ∏_k τ(k)^{t−k} · c`. -/
theorem lemma13_iff_macdonald {t' : ℕ} (hw : ∀ k : ℤ, k ≠ 0 → w ^ k ≠ w ^ (-k)) (c : ℕ → F) :
    (∀ n, ∑ μ ∈ (diagrams n).filter (IsTCore (2 * t' + 1)),
        ((hooks μ).map fun h => tauW w (h - (2 * t' + 1 : ℕ)) * tauW w (h + (2 * t' + 1 : ℕ)) /
          tauW w h ^ 2).prod = c n) ↔
    (∀ n, ∑ μ ∈ (diagrams n).filter (IsTCore (2 * t' + 1)),
        ∏ p ∈ (univ : Finset (Fin (2 * t' + 1) × Fin (2 * t' + 1))).filter (fun p => p.1 < p.2),
          tauW w (uCoding (2 * t' + 1) μ p.1 - uCoding (2 * t' + 1) μ p.2) =
        (-1) ^ t' * (∏ k ∈ Ico 1 (2 * t' + 1), tauW w k ^ (2 * t' + 1 - k)) * c n) := by
  set t := 2 * t' + 1 with ht_def
  have ht : 0 < t := by omega
  set P : F := ∏ k ∈ Ico 1 t, tauW w k ^ (t - k)
  have hP : P ≠ 0 := prod_ne_zero_iff.mpr fun k hk => by
    rw [mem_Ico] at hk; exact pow_ne_zero _ (sub_ne_zero.mpr (hw k (by omega)))
  set C : F := (-1) ^ t'
  have hC : (((if True ∧ t % 4 = 3 then -1 else 1 : Fˣ)) : F) = C := by
    simp only [true_and, C]
    rcases Nat.even_or_odd t' with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [if_neg (by omega), hk, ← two_mul, pow_mul]; simp
    · rw [if_pos (by omega), hk, pow_add, pow_mul]; simp
  have hCC : C * C = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  -- one core at a time: Corollary 4 with `τ = w^k − w^{−k}` (odd)
  have hcore : ∀ μ, IsTCore t μ →
      ((hooks μ).map fun h => tauW w (h - (t : ℕ)) * tauW w (h + (t : ℕ)) / tauW w h ^ 2).prod =
        C * P⁻¹ * ∏ p ∈ (univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2),
          tauW w (uCoding t μ p.1 - uCoding t μ p.2) := by
    intro μ hμ
    have hV := complete ht (stable_of_core ht hμ)
    have e0 := corollary4 ht hμ (tauU w hw) (-1) (Or.inr rfl) (fun x hx => tauU_odd hw x hx)
    have e := congrArg (fun x : Fˣ => (x : F)) e0
    simp only at e
    rw [val_mprod, Units.val_mul, Units.val_div_eq_div_val, hC, Units.coe_prod,
      Units.coe_prod] at e
    simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at e
    have hl : ((hooks μ).map fun h => ((tauU w hw (h - t) : F) * (tauU w hw (h + t) : F)) /
        (tauU w hw h : F) ^ 2) =
        (hooks μ).map fun h => tauW w (h - (t : ℕ)) * tauW w (h + (t : ℕ)) / tauW w h ^ 2 :=
      Multiset.map_congr rfl fun h hh => by
        have h1 := one_le_of_mem_hooks hh
        have h2 : h ≠ t := fun e => hμ h hh (e ▸ dvd_refl _)
        rw [tauU_val hw (by omega), tauU_val hw (by omega), tauU_val hw (by omega)]
    have hp : ∏ k ∈ Ico 1 t, ((tauU w hw k : F)) ^ (t - k) = P :=
      prod_congr rfl fun k hk => by rw [mem_Ico] at hk; rw [tauU_val hw (by omega)]
    have hu : ∏ p ∈ (univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2),
        (tauU w hw (uCoding t μ p.1 - uCoding t μ p.2) : F) =
        ∏ p ∈ (univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2),
          tauW w (uCoding t μ p.1 - uCoding t μ p.2) :=
      prod_congr rfl fun p hp => by
        rw [mem_filter] at hp
        rw [tauU_val hw (sub_ne_zero.mpr fun h => (ne_of_lt hp.2) (uCoding_injective ht hV h))]
    rw [hl, hp, hu] at e
    rw [e, div_eq_mul_inv]
  have hsum : ∀ n, ∑ μ ∈ (diagrams n).filter (IsTCore t),
      ((hooks μ).map fun h => tauW w (h - (t : ℕ)) * tauW w (h + (t : ℕ)) / tauW w h ^ 2).prod =
      C * P⁻¹ * ∑ μ ∈ (diagrams n).filter (IsTCore t),
        ∏ p ∈ (univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2),
          tauW w (uCoding t μ p.1 - uCoding t μ p.2) := fun n => by
    rw [mul_sum]
    exact sum_congr rfl fun μ hμ => hcore μ (mem_filter.mp hμ).2
  constructor
  · intro h n
    rw [← h n, hsum n]
    calc _ = (C * C) * (P * P⁻¹) * ∑ μ ∈ (diagrams n).filter (IsTCore t),
          ∏ p ∈ (univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2),
            tauW w (uCoding t μ p.1 - uCoding t μ p.2) := by
          rw [hCC, mul_inv_cancel₀ hP]; ring
      _ = _ := by ring
  · intro h n
    rw [hsum n, h n]
    calc _ = (C * C) * (P⁻¹ * P) * c n := by ring
      _ = c n := by rw [hCC, inv_mul_cancel₀ hP]; ring

end

end RMT.MultisetHook
