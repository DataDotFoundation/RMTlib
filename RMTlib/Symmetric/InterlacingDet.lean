import RMTlib.Symmetric.JacobiTrudi

/-!
# The interlacing indicator determinant (RMTlib#161)

The condensed edition's `New.UpperBound.ElementaryDivisors.det_interlacing_indicator` (the per-letter
determinant behind `pieriCone`, RH-Dual#239) states: for antitone real `x, y`,
`det [y_c < x_b] = [y_b < x_b ∀ b ∧ x_{b+1} ≤ y_b ∀ b]`. This file proves it over any linear order,
by a different route from the edition's column expansion:

* `det_threshold`: a 0/1 matrix whose row `b` is `1` exactly from column `t b` on, with `t`
  monotone, has determinant `1` if `t b = b` for all `b` (unitriangular) and `0` otherwise (two
  equal rows, or a zero row);
* `det_interlacing_indicator`: **the interlacing indicator determinant**. For antitone `y`, row `b`
  of `[y_c < x_b]` is a threshold row (its zeros are the down-closed set `{c : x_b ≤ y_c}`,
  `lt_card_iff_of_downClosed`), the thresholds are monotone since `x` is antitone, and `t b = b`
  for all `b` is exactly the interlacing `y_b < x_b ≤ y_{b−1}`;
* `det_staircase_gtStep_of_interlacing`: RMTlib's `det_staircase_gtStep` (the Gelfand–Tsetlin step
  as a determinant) is its specialisation `x_i = λ_i − i + 1`, `y_c = μ_c − c` in `ℤ`.

The binding to the condensed edition is `α = ℝ` (RH-Dual's `bridge-condensed`).
-/

open Finset Matrix

namespace RMT.Symmetric

variable {R : Type*} [CommRing R] {k : ℕ}

/-! ## Threshold matrices -/

theorem le_of_strictMono {t : Fin k → ℕ} (ht : StrictMono t) : ∀ b : Fin k, (b : ℕ) ≤ t b := by
  intro b
  induction' hb : (b : ℕ) with n ih generalizing b
  · omega
  · have h1 : n < k := by omega
    have := ht (show (⟨n, h1⟩ : Fin k) < b by rw [Fin.lt_def]; simp; omega)
    have := ih ⟨n, h1⟩ rfl
    omega

theorem add_le_of_strictMono {t : Fin k → ℕ} (ht : StrictMono t) (hk : 0 < k) :
    ∀ b : Fin k, t b + (k - 1 - b) ≤ t ⟨k - 1, by omega⟩ := by
  intro b
  induction' hm : k - 1 - (b : ℕ) with m ih generalizing b
  · have : b = ⟨k - 1, by omega⟩ := Fin.ext (by have := b.isLt; simp; omega)
    rw [this]; simp
  · have h1 : (b : ℕ) + 1 < k := by omega
    have := ht (show b < ⟨b + 1, h1⟩ by rw [Fin.lt_def]; simp)
    have := ih ⟨b + 1, h1⟩ (by simp; omega)
    omega

/-- **The determinant of a threshold matrix**: if row `b` is `1` exactly from column `t b` on, with
`t` monotone, the determinant is `1` when `t b = b` for every `b` (unitriangular), and `0` otherwise
(two equal rows, or a zero row). -/
theorem det_threshold (t : Fin k → ℕ) (ht : Monotone t) :
    det (of fun b c : Fin k => if t b ≤ c then (1 : R) else 0) = if ∀ b, t b = b then 1 else 0 := by
  classical
  split_ifs with h
  · have e : (of fun b c : Fin k => if t b ≤ c then (1 : R) else 0) =
        of fun b c : Fin k => if b ≤ c then (1 : R) else 0 := by
      ext b c; simp only [of_apply, h b, Fin.le_def]
    rw [e, det_of_isUpperTriangular]
    · simp
    · intro b c hcb
      simp only [id] at hcb
      simp only [of_apply]; rw [ite_eq_right (not_le.mpr hcb)]
  · by_cases hinj : Function.Injective t
    · have hs : StrictMono t := ht.strictMono_of_injective hinj
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd (fun b => b.elim0) h
      by_cases hbig : t ⟨k - 1, by omega⟩ < k
      · exfalso; apply h; intro b
        have := le_of_strictMono hs b
        have := add_le_of_strictMono hs hk b
        have := b.isLt
        omega
      · apply det_eq_zero_of_row_eq_zero ⟨k - 1, by omega⟩
        intro c; simp only [of_apply]
        rw [ite_eq_right (by have := c.isLt; omega)]
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨b, b', he, hne⟩ := hinj
      exact det_zero_of_row_eq hne (by ext c; simp only [of_apply, he])

/-! ## The interlacing indicator -/

/-- A down-closed predicate on `Fin k` is `c < (its count)`. -/
theorem lt_card_iff_of_downClosed (P : Fin k → Prop) [DecidablePred P]
    (hP : ∀ c c', c' ≤ c → P c → P c') (c : Fin k) :
    P c ↔ (c : ℕ) < (univ.filter P).card := by
  constructor
  · intro hc
    have : Iic c ⊆ univ.filter P := fun c' hc' => mem_filter.mpr ⟨mem_univ _, hP c c' (mem_Iic.mp hc') hc⟩
    have := card_le_card this
    rw [Fin.card_Iic] at this; omega
  · intro hc
    by_contra hn
    have : univ.filter P ⊆ Iio c := fun c' hc' => by
      rw [mem_Iio]; by_contra hlt
      exact hn (hP c' c (not_lt.mp hlt) (mem_filter.mp hc').2)
    have := card_le_card this
    rw [Fin.card_Iio] at this; omega

variable {α : Type*} [LinearOrder α]

/-- **The interlacing indicator determinant**: for antitone `x, y : Fin k → α`,
`det [y_c < x_b] = [∀ b, y_b < x_b] · [∀ b, x_{b+1} ≤ y_b]`, i.e. `1` exactly when `y` interlaces
`x` from below. This is the statement of the condensed edition's `det_interlacing_indicator`
(RMTlib#161, with `α = ℝ`). -/
theorem det_interlacing_indicator (x y : Fin k → α) (hx : Antitone x) (hy : Antitone y) :
    det (of fun b c : Fin k => if y c < x b then (1 : R) else 0) =
      if (∀ b, y b < x b) ∧ (∀ b c : Fin k, (c : ℕ) = b + 1 → x c ≤ y b) then 1 else 0 := by
  classical
  set t : Fin k → ℕ := fun b => (univ.filter fun c => ¬ y c < x b).card with ht
  have hdown : ∀ b, ∀ c c' : Fin k, c' ≤ c → ¬ y c < x b → ¬ y c' < x b := fun b c c' h hc => by
    rw [not_lt] at hc ⊢; exact hc.trans (hy h)
  have hchar : ∀ b c, ¬ y c < x b ↔ (c : ℕ) < t b := fun b c =>
    lt_card_iff_of_downClosed (fun c => ¬ y c < x b) (hdown b) c
  have hmono : Monotone t := fun b b' hbb' => card_le_card fun c hc => by
    simp only [mem_filter, mem_univ, true_and, not_lt] at hc ⊢
    exact (hx hbb').trans hc
  have e : (of fun b c : Fin k => if y c < x b then (1 : R) else 0) =
      of fun b c : Fin k => if t b ≤ c then (1 : R) else 0 := by
    ext b c; simp only [of_apply]
    have hbc := hchar b c
    by_cases h : y c < x b
    · have : ¬ (c : ℕ) < t b := fun hc => (hbc.mpr hc) h
      rw [ite_eq_left h, ite_eq_left (by omega)]
    · have := hbc.mp h
      rw [ite_eq_right h, ite_eq_right (by omega)]
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
      have hb0 : 0 < (b : ℕ) := by omega
      set c : Fin k := ⟨b - 1, by omega⟩ with hcdef
      have hc : y c < x b := by
        by_contra hn
        have := (hchar b c).mp hn
        simp only [hcdef] at this; omega
      have := h2 c b (by simp only [hcdef]; omega)
      exact lt_irrefl _ (lt_of_lt_of_le hc this)

open Classical in
/-- **`det_staircase_gtStep` is a specialisation of `det_interlacing_indicator`** (RMTlib#161,
RH-Dual#239): with `x_i = λ_i − i + 1` and `y_c = μ_c − c` in `ℤ`, `[y_c < x_b]` is
`[μ_c − c ≤ λ_b − b]` and the interlacing indicator is `GTStep λ μ`. -/
theorem det_staircase_gtStep_of_interlacing {N : ℕ} (lam mu : Fin N → ℕ) (hl : Antitone lam)
    (hm : Antitone mu) :
    det (of fun i c : Fin N => if (mu c : ℤ) - c ≤ (lam i : ℤ) - i then (1 : R) else 0)
      = if RMT.Weyl.GTStep lam mu then 1 else 0 := by
  have hx : Antitone fun i : Fin N => (lam i : ℤ) - i + 1 := fun i j hij => by
    have := hl hij; have : (i : ℕ) ≤ j := hij; push_cast; omega
  have hy : Antitone fun c : Fin N => (mu c : ℤ) - c := fun i j hij => by
    have := hm hij; have : (i : ℕ) ≤ j := hij; push_cast; omega
  have h := det_interlacing_indicator (R := R) _ _ hx hy
  have e : (of fun i c : Fin N => if (mu c : ℤ) - c ≤ (lam i : ℤ) - i then (1 : R) else 0) =
      of fun i c : Fin N => if (mu c : ℤ) - c < (lam i : ℤ) - i + 1 then (1 : R) else 0 := by
    ext i c; simp only [of_apply]; congr 1; apply propext; omega
  rw [e, h]
  congr 1
  apply propext
  unfold RMT.Weyl.GTStep
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun l j hj => by have := h2 l j hj; omega, fun t => by have := h1 t; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun t => by have := h2 t; omega, fun l j hj => by have := h1 l j hj; omega⟩

end RMT.Symmetric
