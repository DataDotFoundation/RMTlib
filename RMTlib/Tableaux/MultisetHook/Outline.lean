import RMTlib.Tableaux.MultisetHook
import RMTlib.Tableaux.MultisetHook.Residue

/-!
# Outline: a Scholze-style restatement of Dehaye–Han, Theorem 1

`RMT.MultisetHook.Statement` follows the paper. This file states the same content in a form
closer to Scholze's way of working: one universal identity in `ℤ^(ℤ)`, a single named step that
involves the vacuum, and the paper's formulas recovered by evaluation. It then proves that the
new statements imply the old ones. The new statements are proved in
`RMTlib.Tableaux.MultisetHook.Maya` (and `…Residue` for the algebra).

## The new statements

The data is the Maya diagram `M(λ) = {λ_i − i − 1}` (`Occ`) with its holes `{j − λ'_j}` (`hole`).

* **N1, cores are `t`-stable** (`CoreStable`): `λ` is a `t`-core iff `M − t ⊆ M`.
* **N2, the sea** (`Sea`): the holes are exactly the complement of `M`, and the hook multiset is
  the multiset of particle–hole differences `x − y` (`x ∈ M`, `y ∉ M`, `y < x`). This is the
  only statement about the vacuum; everything after it is about a set `M ⊆ ℤ`.
* **N3, the abacus** (`Abacus`): for `t`-stable `M`, the `t`-maximal sites `V` form a complete
  residue system, and the hook divisor splits into pair divisors,
  `H = ∑_{a, b ∈ V} pairHooks(a − b)`.
* **N4, the residue identity** (`residue_identity`, proved in `…Residue`): for *every* complete
  residue system `V`, `∑_{a,b} lap(pairHooks(a − b)) + ∑_{i<t} (t − i)·[i] = ∑_{b<a} [a − b]`.
  It holds in every charge sector, not only charge `0`.
* **N5, folded Eq. (2)** (`Folded`): `lap(H) + ∑_{i<t} (t − i)·[i] = ∑_{b<a in V} [a − b]`,
  where `lap[h] = [|h − t|] + [h + t] − 2[h]`. There is no `β` and no `τ(−i)`. This is
  N3 + N4 (`folded_of_abacus`).
* **N6, the charge** (`Charge`): `∑_{a ∈ V} a = −t(t + 1)/2` (the paper's Eq. (8)). This is the
  only place where the shift `(t + 1)/2` (`t₀ ∈ {0, ½}`) matters: a gauge, fixed by `λ` having
  charge `0`.
* **N7, conjugation** (`TransposeV`): `V(λᵀ) = −1 − t − V(λ)`, the fermionic twin.

## Dependencies proved here

* `divisor_iff_folded`: the paper's Eq. (2) in multiset form **is equivalent to** N5. The `β`
  terms are what `h − t` costs over `|h − t|` on hooks `h < t` (`fold_hooks`).
* `size_of_folded`: N5 + N6 ⇒ the paper's Eq. (1). Eq. (1) is the image of N5 under the
  additive character `[k] ↦ k²` (`sqEval`), the infinitesimal version of `τ`.
* `coding_of_charge`: N3 (completeness) + N6 ⇒ `φ_t(λ)` is a `V_t`-coding.
* `transpose_of`: N7 ⇒ the paper's Eq. (6).
* `folded_of_abacus`: N3 + N4 ⇒ N5.

The bijectivity of `φ_t` is proved in `RMTlib.Tableaux.MultisetHook.Bijection`, which concludes
`theorem1 : Theorem1`.
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

open Classical

/-- The particle–hole pairs `(x, y)`: `x ∈ M`, `y ∉ M`, `y < x`. (The window `[−ℓ, λ₁ − 1]` only
makes the set finite; all such pairs lie in it.) -/
def pairs (μ : YoungDiagram) : Finset (ℤ × ℤ) :=
  ((Icc (-(μ.colLen 0 : ℤ)) (μ.rowLen 0 - 1)) ×ˢ (Icc (-(μ.colLen 0 : ℤ)) (μ.rowLen 0 - 1))).filter
    fun p => Occ μ p.1 ∧ ¬ Occ μ p.2 ∧ p.2 < p.1

/-! ### The new statements -/

/-- **N1.** `t`-cores are exactly the `t`-stable Maya diagrams. -/
def CoreStable (t : ℕ) (μ : YoungDiagram) : Prop :=
  IsTCore t μ ↔ ∀ x, Occ μ x → Occ μ (x - t)

/-- **N2, the sea.** Holes are the complement of `M`, and hooks are particle–hole differences. -/
def Sea (μ : YoungDiagram) : Prop :=
  (∀ z, Occ μ z ↔ ¬ ∃ j, hole μ j = z) ∧ toDiv (hooks μ) = ∑ p ∈ pairs μ, pt (p.1 - p.2)

/-- **N3, the abacus.** `V` is a complete residue system and `H = ∑_{a,b ∈ V} pairHooks(a − b)`. -/
def Abacus (t : ℕ) (μ : YoungDiagram) : Prop :=
  Complete t (vSet t μ) ∧
    toDiv (hooks μ) = ∑ a ∈ vSet t μ, ∑ b ∈ vSet t μ, pairHooks t (a - b)

/-- **N5, folded Eq. (2).** `lap(H) + ∑_{i<t} (t − i)·[i] = ∑_{b<a in V} [a − b]`. -/
def Folded (t : ℕ) (μ : YoungDiagram) : Prop :=
  lap t (toDiv (hooks μ)) + ∑ i ∈ Ico 1 t, ((t : ℤ) - i) • pt i =
    ∑ a ∈ vSet t μ, ∑ b ∈ (vSet t μ).filter (· < a), pt (a - b)

/-- **N6, the charge** (Eq. (8)): `2 ∑_{a ∈ V} a = −t(t + 1)`. -/
def Charge (t : ℕ) (μ : YoungDiagram) : Prop :=
  2 * ∑ a ∈ vSet t μ, a = -((t : ℤ) * (t + 1))

/-- **N7, conjugation.** `V(λᵀ) = −1 − t − V(λ)`. -/
def TransposeV (t : ℕ) (μ : YoungDiagram) : Prop :=
  vSet t μ.transpose = (vSet t μ).image fun b => -1 - (t : ℤ) - b

/-! ### N3 + N4 ⇒ N5 -/

theorem folded_of_abacus {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (h : Abacus t μ) :
    Folded t μ := by
  rw [Folded, h.2, map_sum]
  simp only [map_sum]
  exact residue_identity ht h.1

/-! ### The coding as an enumeration of `V` -/

section Coding

variable {t : ℕ} {μ : YoungDiagram}

theorem aCoding_eq (h : (vSet t μ).card = t) (i : Fin t) :
    aCoding t μ i = (vSet t μ).orderEmbOfFin h i.rev := by
  simp [aCoding, h]

theorem aCoding_mem (h : (vSet t μ).card = t) (i : Fin t) : aCoding t μ i ∈ vSet t μ := by
  rw [aCoding_eq h]; exact orderEmbOfFin_mem _ _ _

theorem aCoding_strictAnti (h : (vSet t μ).card = t) : StrictAnti (aCoding t μ) := by
  intro i j hij
  rw [aCoding_eq h, aCoding_eq h]
  exact ((vSet t μ).orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hij)

theorem aCoding_surj (h : (vSet t μ).card = t) {a : ℤ} (ha : a ∈ vSet t μ) :
    ∃ i, aCoding t μ i = a := by
  have : a ∈ Set.range ((vSet t μ).orderEmbOfFin h) := by rw [range_orderEmbOfFin]; exact ha
  obtain ⟨j, rfl⟩ := this
  exact ⟨j.rev, by rw [aCoding_eq h, Fin.rev_rev]⟩

/-- Sums over the coding are sums over `V`. -/
theorem sum_aCoding (h : (vSet t μ).card = t) {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ i, f (aCoding t μ i) = ∑ a ∈ vSet t μ, f a := by
  refine sum_nbij (aCoding t μ) (fun i _ => aCoding_mem h i)
    (fun i _ j _ hij => (aCoding_strictAnti h).injective hij) (fun a ha => ?_) (fun _ _ => rfl)
  obtain ⟨i, rfl⟩ := aCoding_surj h ha
  exact ⟨i, mem_coe.mpr (mem_univ _), rfl⟩

/-- A strictly decreasing enumeration of a `t`-element set is unique. -/
theorem eq_of_strictAnti {V : Finset ℤ} (hV : V.card = t) {f g : Fin t → ℤ}
    (hf : StrictAnti f) (hg : StrictAnti g) (hfV : ∀ i, f i ∈ V) (hgV : ∀ i, g i ∈ V) : f = g := by
  have h1 := orderEmbOfFin_unique hV (f := fun i => f i.rev) (fun i => hfV _)
    (fun i j hij => hf (Fin.rev_lt_rev.mpr hij))
  have h2 := orderEmbOfFin_unique hV (f := fun i => g i.rev) (fun i => hgV _)
    (fun i j hij => hg (Fin.rev_lt_rev.mpr hij))
  funext i
  have := congrFun (h1.trans h2.symm) i.rev
  simpa using this

/-- The pair differences of the coding are the differences `a − b`, `b < a`, in `V`. -/
theorem toDiv_pairDiffs (h : (vSet t μ).card = t) :
    toDiv (pairDiffs (aCoding t μ)) =
      ∑ a ∈ vSet t μ, ∑ b ∈ (vSet t μ).filter (· < a), pt (a - b) := by
  have e1 : toDiv (pairDiffs (aCoding t μ)) =
      ∑ p ∈ (univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2),
        pt (aCoding t μ p.1 - aCoding t μ p.2) := by
    rw [pairDiffs, toDiv_map]; rfl
  have e2 : ∑ a ∈ vSet t μ, ∑ b ∈ (vSet t μ).filter (· < a), pt (a - b) =
      ∑ q ∈ (vSet t μ ×ˢ vSet t μ).filter (fun q => q.2 < q.1), pt (q.1 - q.2) := by
    rw [sum_filter, sum_product]
    exact sum_congr rfl fun a _ => by rw [sum_filter]
  rw [e1, e2]
  refine sum_nbij (fun p => (aCoding t μ p.1, aCoding t μ p.2)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    simp only [mem_filter, mem_product]
    exact ⟨⟨aCoding_mem h _, aCoding_mem h _⟩, aCoding_strictAnti h hp⟩
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext ((aCoding_strictAnti h).injective hpq.1) ((aCoding_strictAnti h).injective hpq.2)
  · rintro ⟨x, y⟩ hq
    simp only [coe_filter, mem_product] at hq
    obtain ⟨⟨ha, hb⟩, hlt⟩ := hq
    obtain ⟨i, rfl⟩ := aCoding_surj h ha
    obtain ⟨j, rfl⟩ := aCoding_surj h hb
    refine ⟨(i, j), ?_, rfl⟩
    simp only [coe_filter, mem_univ, true_and]
    exact (aCoding_strictAnti h).lt_iff_gt.mp hlt

end Coding

/-! ### Folded Eq. (2) ⇔ the paper's Eq. (2) -/

/-- `lap` of a multiset, hook by hook. -/
theorem lap_toDiv (t : ℕ) (m : Multiset ℤ) : lap t (toDiv m) = (m.map (lapPt t)).sum := by
  rw [toDiv, map_multiset_sum, Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun h _ => lap_pt t h)

/-- **The cost of `h − t` over `|h − t|`**: for hooks `h ≥ 1`, `h ≠ t`,
`∑_h [h − t] = ∑_h [|h − t|] + ∑_{i=1}^{t−1} β_i·([−i] − [i])`, with `β_i = #{h = t − i}`. -/
theorem fold_hooks (t : ℕ) (H : Multiset ℤ) (hH : ∀ h ∈ H, 1 ≤ h ∧ h ≠ t) :
    (H.map fun h => pt (h - t)).sum = (H.map fun h => pt |h - t|).sum +
      ∑ i ∈ Ico 1 t, H.count ((t : ℤ) - i) • (pt (-(i : ℤ)) - pt i) := by
  induction H using Multiset.induction_on with
  | empty => simp
  | cons h H ih =>
    have hh := hH h (Multiset.mem_cons_self _ _)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons, add_smul,
      sum_add_distrib]
    rw [ih fun x hx => hH x (Multiset.mem_cons_of_mem hx)]
    have single : ∑ i ∈ Ico 1 t, (if (t : ℤ) - i = h then 1 else 0) • (pt (-(i : ℤ)) - pt i) =
        pt (h - t) - pt |h - t| := by
      rcases lt_or_gt_of_ne hh.2 with hlt | hgt
      · rw [sum_eq_single_of_mem (t - h).toNat (by rw [mem_Ico]; omega)]
        · rw [ite_eq_left (by omega), one_smul, abs_of_neg (by omega)]
          congr 2 <;> omega
        · intro i _ hi; rw [ite_eq_right (by omega), zero_smul]
      · rw [sum_eq_zero fun i hi => by rw [mem_Ico] at hi; rw [ite_eq_right (by omega), zero_smul],
          abs_of_pos (by omega), sub_self]
    rw [single]
    abel

/-- Hooks are positive. -/
theorem one_le_of_mem_hooks {μ : YoungDiagram} {h : ℤ} (hh : h ∈ hooks μ) : 1 ≤ h := by
  obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hh
  have hc' : c ∈ μ := hc
  have h1 := μ.mem_iff_lt_rowLen.mp (show (c.1, c.2) ∈ μ from hc')
  have h2 := μ.mem_iff_lt_colLen.mp (show (c.1, c.2) ∈ μ from hc')
  unfold hook; omega

theorem iff_of_sub_eq {G : Type*} [AddCommGroup G] {a b c d : G} (h : a - b = c - d) :
    a = b ↔ c = d := by
  rw [← sub_eq_zero, h, sub_eq_zero]

/-- **Dependency: the paper's Eq. (2) (multiset form) ⇔ folded Eq. (2) (N5).** -/
theorem divisor_iff_folded {t : ℕ} {μ : YoungDiagram} (hcore : IsTCore t μ)
    (hcard : (vSet t μ).card = t) : divisorLHS t μ = divisorRHS t μ ↔ Folded t μ := by
  have hH : ∀ h ∈ hooks μ, 1 ≤ h ∧ h ≠ t := fun h hh =>
    ⟨one_le_of_mem_hooks hh, fun e => hcore h hh (e ▸ dvd_refl _)⟩
  have hfold := fold_hooks t (hooks μ) hH
  rw [← toDiv_injective.eq_iff, Folded, lap_toDiv]
  simp only [divisorLHS, divisorRHS, toDiv_add, toDiv_nsmul, toDiv_sum, toDiv_singleton,
    toDiv_map, toDiv_pairDiffs hcard]
  have hnat : ∀ i ∈ Ico 1 t, (beta t μ i + t - i) • pt (i : ℤ) =
      beta t μ i • pt (i : ℤ) + ((t : ℤ) - i) • pt (i : ℤ) := fun i hi => by
    rw [mem_Ico] at hi
    rw [show beta t μ i + t - i = beta t μ i + (t - i) by omega, add_smul,
      ← Nat.cast_smul_eq_nsmul ℤ (t - i), Nat.cast_sub hi.2.le]
  have hlap : ((hooks μ).map (lapPt t)).sum = ((hooks μ).map fun h => pt |h - t|).sum +
      ((hooks μ).map fun h => pt (h + t)).sum - 2 • toDiv (hooks μ) := by
    rw [show lapPt t = fun h => pt |h - t| + pt (h + t) - 2 • pt h from rfl]
    simp only [Multiset.sum_map_add, Multiset.sum_map_sub, Multiset.sum_map_nsmul]; rfl
  rw [sum_congr rfl hnat, sum_add_distrib, hfold, hlap]
  simp only [beta, smul_sub, sum_sub_distrib]
  apply iff_of_sub_eq
  abel

/-! ### Eq. (1) as the `k²` character of N5 -/

/-- The additive character `[k] ↦ k²` (the infinitesimal version of a weight `τ`). -/
def sqEval : (ℤ →₀ ℤ) →+ ℤ := Finsupp.liftAddHom fun k => zmultiplesHom ℤ (k ^ 2)

theorem sqEval_pt (k : ℤ) : sqEval (pt k) = k ^ 2 := by simp [sqEval]

theorem sqEval_smul_pt (n k : ℤ) : sqEval (n • pt k) = n * k ^ 2 := by
  rw [map_zsmul, sqEval_pt, smul_eq_mul]

/-- `12 ∑_{i=1}^{t−1} (t − i) i² = t²(t² − 1)`. -/
theorem sum_weighted_sq (t : ℕ) : 12 * ∑ i ∈ Ico 1 t, ((t : ℤ) - i) * (i : ℤ) ^ 2 =
    (t : ℤ) ^ 2 * ((t : ℤ) ^ 2 - 1) := by
  have sq : ∀ n : ℕ, 6 * ∑ i ∈ Ico 1 (n + 1), (i : ℤ) ^ 2 = n * (n + 1) * (2 * n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_Ico_succ_top (by omega), mul_add, ih]; push_cast; ring
  induction t with
  | zero => simp
  | succ t ih =>
    have e : ∑ i ∈ Ico 1 (t + 1), (((t + 1 : ℕ) : ℤ) - i) * (i : ℤ) ^ 2 =
        ∑ i ∈ Ico 1 t, ((t : ℤ) - i) * (i : ℤ) ^ 2 + ∑ i ∈ Ico 1 (t + 1), (i : ℤ) ^ 2 := by
      rw [show ∑ i ∈ Ico 1 (t + 1), (((t + 1 : ℕ) : ℤ) - i) * (i : ℤ) ^ 2 =
          ∑ i ∈ Ico 1 (t + 1), (((t : ℤ) - i) * (i : ℤ) ^ 2 + (i : ℤ) ^ 2) from
            sum_congr rfl fun i _ => by push_cast; ring, sum_add_distrib]
      rcases Nat.eq_zero_or_pos t with rfl | htp
      · simp
      rw [sum_Ico_succ_top (show 1 ≤ t by omega) (fun i => ((t : ℤ) - i) * (i : ℤ) ^ 2),
        sub_self, zero_mul, add_zero]
    rw [e, mul_add, ih, show (12 : ℤ) * ∑ i ∈ Ico 1 (t + 1), (i : ℤ) ^ 2 =
      2 * (6 * ∑ i ∈ Ico 1 (t + 1), (i : ℤ) ^ 2) by ring, sq t]
    push_cast; ring

/-- **Dependency: N5 + N6 ⇒ the paper's Eq. (1).** -/
theorem size_of_folded {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hV : Complete t (vSet t μ))
    (hF : Folded t μ) (hQ : Charge t μ) :
    (μ.cells.card : ℚ) = (∑ i, vCoding t μ i ^ 2) / (2 * t) - ((t : ℚ) ^ 2 - 1) / 24 := by
  set V := vSet t μ
  -- evaluate N5 on `[k] ↦ k²`
  have e := congrArg sqEval hF
  rw [map_add, lap_toDiv, map_multiset_sum, Multiset.map_map, map_sum] at e
  simp only [Function.comp_def, lapPt, map_add, map_sub, map_nsmul, sqEval_pt, sqEval_smul_pt,
    map_sum, sq_abs] at e
  have hlap : ∀ h : ℤ, (h - t) ^ 2 + (h + t) ^ 2 - ((2 : ℕ) : ℤ) * h ^ 2 = 2 * (t : ℤ) ^ 2 :=
    fun h => by push_cast; ring
  simp only [hlap, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul] at e
  have hcard : (hooks μ).card = μ.cells.card := by simp [hooks]
  rw [hcard] at e
  -- the pair sum: `2 ∑_{b<a} (a − b)² = 2t ∑ a² − 2 (∑ a)²`
  have hsym := congrArg sqEval (sum_sym V (fun e => pt |e|) fun a _ b _ _ => by
    rw [show b - a = -(a - b) by ring, abs_neg])
  simp only [map_add, map_nsmul, map_sum, sqEval_pt, sq_abs, abs_zero, zero_pow two_ne_zero,
    smul_zero, zero_add, nsmul_eq_mul, Nat.cast_ofNat] at hsym
  have hexp : ∑ a ∈ V, ∑ b ∈ V, (a - b) ^ 2 =
      2 * V.card * ∑ a ∈ V, a ^ 2 - 2 * (∑ a ∈ V, a) ^ 2 := by
    have h2 : ∀ a b : ℤ, (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * (a * b) := fun a b => by ring
    simp only [h2, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
      ← sum_mul_sum]
    ring
  have hS := sum_weighted_sq t
  rw [hV.card] at hexp
  -- move to `ℚ`
  have hvsum : ∑ i, vCoding t μ i ^ 2 =
      ∑ a ∈ V, (a : ℚ) ^ 2 + (t + 1) * ∑ a ∈ V, (a : ℚ) + t * (((t : ℚ) + 1) / 2) ^ 2 := by
    simp only [vCoding]
    rw [sum_aCoding hV.card (fun a : ℤ => ((a : ℚ) + ((t : ℚ) + 1) / 2) ^ 2)]
    simp only [add_sq, sum_add_distrib, sum_const, show (vSet t μ).card = t from hV.card,
      nsmul_eq_mul, ← sum_mul, ← mul_sum]
    ring
  rw [hvsum]
  set n : ℚ := (μ.cells.card : ℚ)
  set X : ℚ := ∑ a ∈ V, (a : ℚ) ^ 2
  set Y : ℚ := ∑ a ∈ V, (a : ℚ)
  set P : ℚ := ∑ a ∈ V, ∑ b ∈ V.filter (· < a), ((a : ℚ) - b) ^ 2
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast ht.ne'
  have hY : Y = -((t : ℚ) * (t + 1)) / 2 := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hQ; push_cast at this
    simp only [Y]; linarith
  have hX : X = (P + Y ^ 2) / t := by
    rw [eq_div_iff htq]
    have := congrArg (fun z : ℤ => (z : ℚ)) (hsym.symm.trans hexp); push_cast at this
    simp only [X, Y, P]; linarith
  have hn : n = (P - (t : ℚ) ^ 2 * ((t : ℚ) ^ 2 - 1) / 12) / (2 * (t : ℚ) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    have e' := congrArg (fun z : ℤ => (z : ℚ)) e; push_cast at e'
    have hS' := congrArg (fun z : ℤ => (z : ℚ)) hS; push_cast at hS'
    simp only [n, P]; linarith
  rw [hn, hX, hY]
  field_simp
  ring

/-! ### The coding conditions and conjugation -/

/-- **Dependency: N3 (completeness) + N6 ⇒ `φ_t(λ)` is a `V_t`-coding.** -/
theorem coding_of_charge {t : ℕ} {μ : YoungDiagram} (hV : Complete t (vSet t μ))
    (hQ : Charge t μ) : IsVCoding t (vCoding t μ) := by
  refine ⟨?_, ?_, aCoding t μ, fun i => rfl, ?_⟩
  · intro i j hij
    simp only [vCoding, add_lt_add_iff_right, Int.cast_lt]
    exact aCoding_strictAnti hV.card hij
  · simp only [vCoding, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [sum_aCoding hV.card (fun a : ℤ => (a : ℚ))]
    have := congrArg (fun z : ℤ => (z : ℚ)) hQ; push_cast at this
    linarith
  · intro i j hij
    exact (aCoding_strictAnti hV.card).injective
      (hV.inj _ (aCoding_mem hV.card i) _ (aCoding_mem hV.card j) hij)

/-- **Dependency: N7 ⇒ the paper's Eq. (6)**, `v(λᵀ) = −rev v(λ)`. -/
theorem transpose_of {t : ℕ} {μ : YoungDiagram} (hV : Complete t (vSet t μ))
    (hV' : Complete t (vSet t μ.transpose)) (hT : TransposeV t μ) :
    vCoding t μ.transpose = fun i => -vCoding t μ i.rev := by
  have ha : aCoding t μ.transpose = fun i => -1 - t - aCoding t μ i.rev := by
    apply eq_of_strictAnti hV'.card (aCoding_strictAnti hV'.card)
    · intro i j hij
      have := aCoding_strictAnti hV.card (Fin.rev_lt_rev.mpr hij)
      simp only; omega
    · exact aCoding_mem hV'.card
    · intro i; rw [hT]; exact mem_image_of_mem _ (aCoding_mem hV.card _)
  funext i
  simp only [vCoding, ha]
  push_cast
  ring

end

end RMT.MultisetHook
