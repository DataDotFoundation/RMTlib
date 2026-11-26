/-
Copyright (c) 2026 <contributor>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <contributor>
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Interval.Finset.Fin

/-!
# Determinants of threshold and interlacing indicator matrices

* `Matrix.det_threshold`: if row `b` of a `0/1` matrix is `1` exactly from column `t b` on, with
  `t` monotone, the determinant is `1` when `t b = b` for every `b` (the matrix is unitriangular),
  and `0` otherwise (two equal rows, or a zero row).
* `Matrix.det_interlacing_indicator`: for antitone `x y : Fin k → α` in a linear order,
  `det [y c < x b] = 1` if `y` interlaces `x` from below (`y b < x b` and `x (b + 1) ≤ y b`), and
  `0` otherwise.

The interlacing determinant appears in Pieri rules and Gelfand–Tsetlin patterns: with
`x b = λ b - b + 1` and `y c = μ c - c`, it is the indicator that `λ / μ` is a horizontal strip.
-/

open Finset

namespace Matrix

variable {R : Type*} [CommRing R] {k : ℕ}

private theorem val_le_of_strictMono {t : Fin k → ℕ} (ht : StrictMono t) (b : Fin k) :
    (b : ℕ) ≤ t b := by
  obtain ⟨n, hn⟩ := b
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have := ht (show (⟨n, by omega⟩ : Fin k) < ⟨n + 1, hn⟩ from Fin.mk_lt_mk.mpr n.lt_succ_self)
    have := ih (by omega)
    simp only at this ⊢; omega

private theorem add_le_of_strictMono {t : Fin k → ℕ} (ht : StrictMono t) (hk : 0 < k)
    (b : Fin k) : t b + (k - 1 - b) ≤ t ⟨k - 1, by omega⟩ := by
  obtain ⟨b, hb⟩ := b
  induction hm : k - 1 - b generalizing b with
  | zero => obtain rfl : b = k - 1 := by omega
            simp
  | succ m ih =>
    have := ht (show (⟨b, hb⟩ : Fin k) < ⟨b + 1, by omega⟩ from Fin.mk_lt_mk.mpr b.lt_succ_self)
    have := ih (b + 1) (by omega) (by omega)
    omega

/-- **The determinant of a threshold matrix**: if row `b` is `1` exactly from column `t b` on, with
`t` monotone, the determinant is `1` when `t b = b` for every `b`, and `0` otherwise. -/
theorem det_threshold (t : Fin k → ℕ) (ht : Monotone t) :
    det (of fun b c : Fin k => if t b ≤ c then (1 : R) else 0) =
      if ∀ b, t b = b then 1 else 0 := by
  classical
  split_ifs with h
  · have e : (of fun b c : Fin k => if t b ≤ c then (1 : R) else 0) =
        of fun b c : Fin k => if b ≤ c then (1 : R) else 0 := by
      ext b c; simp only [of_apply, h b, Fin.le_def]
    rw [e, det_of_isUpperTriangular]
    · simp
    · intro b c hcb
      simp only [of_apply]
      exact ite_eq_right (not_le.mpr hcb)
  · by_cases hinj : Function.Injective t
    · have hs : StrictMono t := ht.strictMono_of_injective hinj
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd (fun b => b.elim0) h
      by_cases hbig : t ⟨k - 1, by omega⟩ < k
      · refine absurd (fun b => ?_) h
        have := val_le_of_strictMono hs b
        have := add_le_of_strictMono hs hk b
        have := b.isLt
        omega
      · refine det_eq_zero_of_row_eq_zero ⟨k - 1, by omega⟩ fun c => ?_
        simp only [of_apply]
        exact ite_eq_right (by have := c.isLt; omega)
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨b, b', he, hne⟩ := hinj
      exact det_zero_of_row_eq hne (by ext c; simp only [of_apply, he])

/-- A down-closed predicate on `Fin k` holds exactly below its number of solutions. -/
private theorem lt_card_iff_of_downClosed (P : Fin k → Prop) [DecidablePred P]
    (hP : ∀ c c', c' ≤ c → P c → P c') (c : Fin k) :
    P c ↔ (c : ℕ) < (univ.filter P).card := by
  constructor
  · intro hc
    have := card_le_card fun c' (hc' : c' ∈ Iic c) =>
      mem_filter.mpr ⟨mem_univ _, hP c c' (mem_Iic.mp hc') hc⟩
    rw [Fin.card_Iic] at this; omega
  · intro hc
    by_contra hn
    have := card_le_card fun c' (hc' : c' ∈ univ.filter P) => mem_Iio.mpr
      (lt_of_not_ge fun hle => hn (hP c' c hle (mem_filter.mp hc').2))
    rw [Fin.card_Iio] at this; omega

variable {α : Type*} [LinearOrder α]

/-- **The interlacing indicator determinant**: for antitone `x y : Fin k → α`, the determinant of
`[y c < x b]` is `1` if `y` interlaces `x` from below (`y b < x b` and `x (b + 1) ≤ y b`), and `0`
otherwise. -/
theorem det_interlacing_indicator (x y : Fin k → α) (hx : Antitone x) (hy : Antitone y) :
    det (of fun b c : Fin k => if y c < x b then (1 : R) else 0) =
      if (∀ b, y b < x b) ∧ (∀ b c : Fin k, (c : ℕ) = b + 1 → x c ≤ y b) then 1 else 0 := by
  classical
  set t : Fin k → ℕ := fun b => #{c | ¬ y c < x b}
  have hchar (b c : Fin k) : ¬ y c < x b ↔ (c : ℕ) < t b :=
    lt_card_iff_of_downClosed (fun c => ¬ y c < x b)
      (fun c c' h hc => by rw [not_lt] at hc ⊢; exact hc.trans (hy h)) c
  have hmono : Monotone t := fun b b' hbb' => card_le_card fun c hc => by
    simp only [mem_filter, mem_univ, true_and, not_lt] at hc ⊢
    exact (hx hbb').trans hc
  have e : (of fun b c : Fin k => if y c < x b then (1 : R) else 0) =
      of fun b c : Fin k => if t b ≤ c then (1 : R) else 0 := by
    ext b c
    simp only [of_apply]
    congr 1
    rw [← not_lt, ← hchar, not_not]
  rw [e, det_threshold t hmono]
  congr 1
  apply propext
  constructor
  · intro h
    refine ⟨fun b => ?_, fun b c hc => ?_⟩
    · by_contra hn
      have := (hchar b b).mp hn
      rw [h b] at this; omega
    · exact not_lt.mp ((hchar c b).mpr (by rw [h c]; omega))
  · rintro ⟨h1, h2⟩ b
    apply le_antisymm
    · by_contra hlt
      exact (hchar b b).mpr (by omega) (h1 b)
    · by_contra hlt
      have hc : y ⟨b - 1, by omega⟩ < x b := by
        by_contra hn
        have := (hchar b _).mp hn
        simp only at this; omega
      exact lt_irrefl _ (hc.trans_le (h2 ⟨b - 1, by omega⟩ b (by simp only; omega)))

end Matrix
