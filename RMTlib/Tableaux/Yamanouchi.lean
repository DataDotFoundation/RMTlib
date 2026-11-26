import RMTlib.Tableaux.HookLengthFormula

/-!
# Yamanouchi words

A word `w : Fin n → Fin N` is Yamanouchi of shape `ν` (`IsYam`) when every prefix has partition
content and the whole word has content `ν`: reading letter `t` as "put box `t` in row `w t`", it
is a path `∅ → ν` in Young's lattice. Removing the last letter gives the branching recursion,
so these words are counted by `fSYT` (`card_isYam`).
-/

open Finset
open scoped Nat

namespace RMT

variable {N : ℕ}

/-- The number of letters `i` among the first `t` letters of the word `w`. -/
def cnt {n : ℕ} (w : Fin n → Fin N) (t : ℕ) (i : Fin N) : ℕ :=
  ∑ s, if s.val < t ∧ w s = i then 1 else 0

/-- A Yamanouchi word of shape `ν`: every prefix has partition content, and the whole word has
content `ν`. Reading letter `t` as "put box `t` in row `w t`" makes it a path `∅ → ν` in
Young's lattice. -/
def IsYam {n : ℕ} (ν : Fin N → ℕ) (w : Fin n → Fin N) : Prop :=
  (∀ t, Antitone (cnt w t)) ∧ cnt w n = ν

theorem cnt_snoc {n : ℕ} (w' : Fin n → Fin N) (a : Fin N) (t : ℕ) (i : Fin N) :
    cnt (Fin.snoc (α := fun _ => Fin N) w' a) t i =
      cnt w' t i + if n < t ∧ a = i then 1 else 0 := by
  simp only [cnt]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem cnt_of_le {n : ℕ} (w : Fin n → Fin N) {t : ℕ} (ht : n ≤ t) : cnt w t = cnt w n := by
  funext i
  refine sum_congr rfl fun s _ => ?_
  have := s.isLt
  simp only [show s.val < t from by omega, this, true_and]

theorem corner_of_antitone_removeBox {ν : Fin N → ℕ} {a : Fin N} (hpos : 0 < ν a)
    (h : Antitone (removeBox ν a)) : IsCorner ν a = true := by
  simp only [IsCorner, hpos, decide_true, Bool.true_and]
  split_ifs with ha
  · have := h (show a ≤ ⟨a.val + 1, ha⟩ from Fin.le_def.mpr (Nat.le_succ _))
    have hne : (⟨a.val + 1, ha⟩ : Fin N) ≠ a := by simp [Fin.ext_iff]
    simp only [removeBox, Function.update_self, Function.update_of_ne hne] at this
    simp only [decide_eq_true_eq]
    omega
  · rfl

theorem isYam_snoc {n : ℕ} (ν : Fin N → ℕ) (w' : Fin n → Fin N) (a : Fin N) :
    IsYam ν (Fin.snoc (α := fun _ => Fin N) w' a) ↔
      Antitone ν ∧ 0 < ν a ∧ IsYam (removeBox ν a) w' := by
  have big : ∀ t, n < t → cnt w' n = removeBox ν a → 0 < ν a →
      cnt (Fin.snoc (α := fun _ => Fin N) w' a) t = ν := by
    intro t ht hc hpos
    funext i
    rw [cnt_snoc, cnt_of_le w' ht.le, hc]
    by_cases hi : a = i
    · subst hi; simp [removeBox, ht]; omega
    · simp [removeBox, Function.update_of_ne (Ne.symm hi), hi]
  have small : ∀ t, t ≤ n → cnt (Fin.snoc (α := fun _ => Fin N) w' a) t = cnt w' t := by
    intro t ht
    funext i
    rw [cnt_snoc]
    simp [show ¬ n < t by omega]
  constructor
  · rintro ⟨hA, hc⟩
    have hc' : ∀ i, cnt w' n i + (if a = i then 1 else 0) = ν i := by
      intro i
      have := congrFun hc i
      rw [cnt_snoc, cnt_of_le w' (Nat.le_succ n)] at this
      simpa using this
    have hpos : 0 < ν a := by have := hc' a; simp at this; omega
    have hcnt : cnt w' n = removeBox ν a := by
      funext i
      have := hc' i
      by_cases hi : a = i
      · subst hi; simp [removeBox] at this ⊢; omega
      · simp [removeBox, Function.update_of_ne (Ne.symm hi), hi] at this ⊢; omega
    refine ⟨by rw [← hc]; exact hA _, hpos, fun t => ?_, hcnt⟩
    rcases le_or_gt t n with ht | ht
    · rw [← small t ht]; exact hA t
    · rw [cnt_of_le w' ht.le, ← small n le_rfl]; exact hA n
  · rintro ⟨hν, hpos, hA, hc⟩
    refine ⟨fun t => ?_, big _ (Nat.lt_succ_self n) hc hpos⟩
    rcases le_or_gt t n with ht | ht
    · rw [small t ht]; exact hA t
    · rw [big t ht hc hpos]; exact hν

/-- **Yamanouchi words of shape `ν` are counted by `fSYT`.** -/
theorem card_isYam (n : ℕ) :
    ∀ ν : Fin N → ℕ, Antitone ν → ∑ i, ν i = n →
      Nat.card {w : Fin n → Fin N // IsYam ν w} = fSYT n ν := by
  induction n with
  | zero =>
    intro ν hν hs
    have h0 : ∀ i, ν i = 0 := fun i => (sum_eq_zero_iff.mp hs) i (mem_univ _)
    simp only [fSYT, hs, ite_true]
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨inferInstance, ⟨⟨Fin.elim0, fun t i j _ => by simp [cnt], ?_⟩⟩⟩
    funext i
    simp [cnt, h0]
  | succ n ih =>
    intro ν hν hs
    rw [fSYT, ite_eq_right (by omega), sum_filter]
    rw [← Nat.card_congr ((Fin.snocEquiv fun _ => Fin N).subtypeEquiv
      (p := fun x => IsYam ν ((Fin.snocEquiv fun _ => Fin N) x)) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.subtypeEquivRight
        (p := fun x => IsYam ν ((Fin.snocEquiv fun _ => Fin N) x)) (q := fun x : Fin N × (Fin n → Fin N) =>
        IsYam ν (Fin.snoc (α := fun _ => Fin N) x.2 x.1)) fun x => Iff.rfl),
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
        (fun a (w' : Fin n → Fin N) => IsYam ν (Fin.snoc (α := fun _ => Fin N) w' a))),
      Nat.card_sigma]
    refine sum_congr rfl fun a _ => ?_
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun w' => isYam_snoc ν w' a)]
    split_ifs with hc
    · obtain ⟨ha, hpos⟩ := removeBox_antitone hν hc
      rw [← ih _ ha (by have := sum_removeBox hpos; omega)]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun w' =>
        ⟨fun h => h.2.2, fun h => ⟨hν, hpos, h⟩⟩)
    · rw [Nat.card_eq_zero]
      left
      refine ⟨fun ⟨w', _, hpos, hA, hcw⟩ => ?_⟩
      have := corner_of_antitone_removeBox hpos (hcw ▸ hA n)
      simp [this] at hc

end RMT
