import RMTlib.Fock.Casimir
import RMTlib.Tableaux.Yamanouchi

/-!
# The Fock diagonal for every shape, from a Casimir

For an `N × N` matrix of variables `X` and partitions `λ, μ ⊢ m`:

  `⟨s_λ(X), s_μ(X)⟩_Fock = δ_{λμ} ∏_{□ ∈ λ} (N + c(□))`   (`fischer_sX_sX_of_casimir`),

for all partitions of the same size, with any number of rows, **given** a Fock self-adjoint
operator `T` with `T s_κ(X) = e(κ) s_κ(X)`, `e(κ) = N|κ| + 2 Σ_{□ ∈ κ} c(□)` (`casEig`). The
Casimir `C = Σ L_{ab} L_{ba}` of the left `gl_N` action is Fock self-adjoint
(`RMT.Fock.fischer_cas`); `fischer_sX_sX_of_cas` states the diagonal with the eigenvalue of `C` as
the only hypothesis. This is the reduction of `bridge/links/fock-norm.md` §6.4.

The induction runs on shapes with an empty last row (`fischer_sX_sX_of_casimir_aux`), so that
Pieri sees every addable box; an empty row changes neither `s_λ(X)` nor the weight
(`sX_padZero`, `wQ_padZero`).

## The induction (on `m = |λ| = |μ|`)

* If `e(λ) ≠ e(μ)`, then `⟨s_λ, s_μ⟩ = 0` because `T` is self-adjoint (`fischer_sX_eq_zero_of_eig`).
* Otherwise, remove a corner `□` of `λ`: `λ = ν + □`. By Pieri (`RMT.Fock.trX_mul_sX`),
  `tr X · s_ν = Σ_{□'} s_{ν+□'}`. The addable boxes of `ν` have pairwise distinct contents
  (`content_injective`), and `e(ν + □') = e(ν) + N + 2c(□')` (`casEig_addBox`), so every
  `s_{ν+□'}` with `□' ≠ □` is orthogonal to `s_μ`. Hence
  `⟨s_λ, s_μ⟩ = ⟨tr X · s_ν, s_μ⟩ = Σ_i (N + c_i) ⟨s_ν, s_{μ − e_i}⟩` (`RMT.Fock.trD_sX`).
* By induction, the only term left is `μ − e_i = ν`; then `e(μ) = e(λ)` forces the box of `μ/ν` to
  have the content of `□`, so `μ = λ`, and the term is `(N + c(□)) w(ν) = w(λ)`.

The weight is assembled box by box twice: the factor `N + c` by `Δ`, and the separation of the
boxes by their content `c` by the Casimir. Rows, columns and the power sums `p_j`, `j ≥ 2`, are not
used.

**`ω`-symmetry.** Transposing `λ` sends `e^{(N)}` to `−e^{(−N)}` (`casEig` is
`N|λ| + 2Σc`), and the weight `∏ (N + c)` to `(−1)^{|λ|} ∏ (−N + c)`
(`RMT.Places.archimedean_contentProd_transpose`). The same induction, with columns in place of
rows (Pieri for `e₁ = p₁` adds a box to a column, and the addable boxes of a column partition
also have distinct contents), would give the fermionic statement; the fermionic Fock space is
not formalised.
-/

open MvPolynomial Finset

namespace RMT.Fock

variable {N : ℕ}

variable (N) in
/-- The Casimir eigenvalue `e(λ) = N|λ| + 2 Σ_{□ ∈ λ} c(□) = Σ_i λ_i (N + λ_i − 1 − 2i)`. -/
def casEig {l : ℕ} (ν : Fin l → ℕ) : ℚ := ∑ i, (ν i : ℚ) * ((N : ℚ) + ν i - 1 - 2 * i)

/-- **Adding a box of content `c` raises `e` by `N + 2c`.** -/
theorem casEig_addBox {l : ℕ} (ν : Fin l → ℕ) (k : Fin l) :
    casEig N (addBox ν k) = casEig N ν + N + 2 * ((ν k : ℚ) - k) := by
  classical
  have h : casEig N (addBox ν k) - casEig N ν = N + 2 * ((ν k : ℚ) - k) := by
    rw [casEig, casEig, ← sum_sub_distrib, Fintype.sum_eq_single k fun i hi => by
      simp [addBox, Function.update_of_ne hi]]
    simp only [addBox, Function.update_self]
    push_cast
    ring
  linarith

/-- **The addable boxes of a partition have pairwise distinct contents**: `ν_i − i` is strictly
decreasing. -/
theorem content_injective {l : ℕ} {ν : Fin l → ℕ} (hν : Antitone ν) {i k : Fin l}
    (h : (ν i : ℚ) - i = (ν k : ℚ) - k) : i = k := by
  have h' : (ν i : ℤ) - i = (ν k : ℤ) - k := by exact_mod_cast h
  rcases lt_trichotomy i k with hik | hik | hik
  · have := hν hik.le
    have : (i : ℕ) < k := hik
    omega
  · exact hik
  · have := hν hik.le
    have : (k : ℕ) < i := hik
    omega

/-- Adding a box, as an integer vector. -/
theorem cast_addBox {l : ℕ} (ν : Fin l → ℕ) (k : Fin l) :
    (fun i => ((addBox ν k i : ℕ) : ℤ)) = Function.update (fun i => (ν i : ℤ)) k ((ν k : ℤ) + 1) := by
  funext i
  by_cases h : i = k
  · subst h; simp [addBox]
  · simp [addBox, Function.update_of_ne h]

/-- Removing a box, as an integer vector. -/
theorem cast_removeBox {l : ℕ} {ν : Fin l → ℕ} {k : Fin l} (hk : 0 < ν k) :
    (fun i => ((removeBox ν k i : ℕ) : ℤ)) = Function.update (fun i => (ν i : ℤ)) k ((ν k : ℤ) - 1) := by
  funext i
  by_cases h : i = k
  · subst h; simp [removeBox]; omega
  · simp [removeBox, Function.update_of_ne h]

/-- A nonempty partition has a corner. -/
theorem exists_corner {l : ℕ} {ν : Fin l → ℕ} (hs : ∑ i, ν i ≠ 0) :
    ∃ k, IsCorner ν k = true := by
  classical
  have hne : (univ.filter fun i => 0 < ν i).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
    exact hs (sum_eq_zero fun i _ => by have := h (mem_univ i); omega)
  set k := (univ.filter fun i => 0 < ν i).max' hne
  have hk : 0 < ν k := (mem_filter.mp (max'_mem _ hne)).2
  refine ⟨k, ?_⟩
  simp only [IsCorner, hk, decide_true, Bool.true_and]
  split_ifs with h
  · simp only [decide_eq_true_eq]
    by_contra hle
    have : (⟨k.val + 1, h⟩ : Fin l) ≤ k :=
      le_max' _ _ (mem_filter.mpr ⟨mem_univ _, by omega⟩)
    simp [Fin.le_def] at this
  · rfl

section Diagonal

variable (T : MvPolynomial (Fin N × Fin N) ℚ → MvPolynomial (Fin N × Fin N) ℚ)

/-- **Different eigenvalues, orthogonal**: if `T` is Fock self-adjoint and `s_λ, s_μ` are
eigenvectors with eigenvalues `e(λ) ≠ e(μ)`, they are Fock orthogonal. -/
theorem fischer_sX_eq_zero_of_eig {l : ℕ}
    (hadj : ∀ f g, fischer (T f) g = fischer f (T g)) {ν μ : Fin l → ℕ}
    (hν : T (sX N fun i => (ν i : ℤ)) = casEig N ν • sX N fun i => (ν i : ℤ))
    (hμ : T (sX N fun i => (μ i : ℤ)) = casEig N μ • sX N fun i => (μ i : ℤ))
    (hne : casEig N ν ≠ casEig N μ) :
    fischer (sX N fun i => (ν i : ℤ)) (sX N fun i => (μ i : ℤ)) = 0 := by
  have h := hadj (sX N fun i => (ν i : ℤ)) (sX N fun i => (μ i : ℤ))
  rw [hν, hμ, smul_eq_C_mul, smul_eq_C_mul, fischer_C_mul_left, fischer_C_mul_right] at h
  have : (casEig N ν - casEig N μ) * fischer (sX N fun i => (ν i : ℤ)) (sX N fun i => (μ i : ℤ))
      = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

/-- **The Fock diagonal for every shape, given a Casimir**: if `T` is Fock self-adjoint and
`T s_λ(X) = e(λ) s_λ(X)` for every partition `λ`, then
`⟨s_λ(X), s_μ(X)⟩_Fock = δ_{λμ} ∏_{□ ∈ λ} (N + c(□))` for all partitions `λ, μ ⊢ m`, written with
`l + 1 ≥ m` rows. -/
theorem fischer_sX_sX_of_casimir_aux {l : ℕ}
    (hadj : ∀ f g, fischer (T f) g = fischer f (T g))
    (heig : ∀ ν : Fin (l + 1) → ℕ, Antitone ν →
      T (sX N fun i => (ν i : ℤ)) = casEig N ν • sX N fun i => (ν i : ℤ)) :
    ∀ m : ℕ, ∀ ν μ : Fin (l + 1) → ℕ, Antitone ν → Antitone μ → ν (Fin.last l) = 0 →
      μ (Fin.last l) = 0 → ∑ i, ν i = m → ∑ i, μ i = m →
      fischer (sX N fun i => (ν i : ℤ)) (sX N fun i => (μ i : ℤ)) = if ν = μ then wQ N ν else 0 := by
  classical
  intro m
  induction m with
  | zero =>
    intro ν μ _ _ _ _ hsν hsμ
    have h0 : ∀ κ : Fin (l + 1) → ℕ, ∑ i, κ i = 0 → κ = 0 := fun κ hs => funext fun i => by
      have := single_le_sum (fun j _ => Nat.zero_le (κ j)) (mem_univ i); simp at this ⊢; omega
    rw [h0 ν hsν, h0 μ hsμ, if_pos rfl]
    simp only [Pi.zero_apply, Nat.cast_zero]
    rw [sX_zero, fischer_one_one]
    simp [wQ]
  | succ m ih =>
    intro lam μ hlam hμ hlamlast hμlast hslam hsμ
    obtain ⟨k, hk⟩ := exists_corner (ν := lam) (by omega)
    obtain ⟨hνa, hkpos⟩ := removeBox_antitone hlam hk
    set ν := removeBox lam k with hνdef
    have hlamν : lam = addBox ν k := (addBox_removeBox hkpos).symm
    have hsν : ∑ i, ν i = m := by
      have := sum_removeBox hkpos
      rw [← hνdef] at this
      omega
    have hlast : ν (Fin.last l) = 0 := by
      simp only [hνdef, removeBox, Function.update_apply, hlamlast]
      split_ifs with h
      · rw [← h, hlamlast]
      · rfl
    by_cases he : casEig N lam = casEig N μ
    swap
    · rw [fischer_sX_eq_zero_of_eig T hadj (heig lam hlam) (heig μ hμ) he, if_neg]
      rintro rfl
      exact he rfl
    -- the Pieri terms other than `λ` are orthogonal to `s_μ`
    have hpieri := trX_mul_sX (N := N) (fun i => (ν i : ℤ)) (by simp [hlast])
    have hother : ∀ i, i ≠ k →
        fischer (sX N (Function.update (fun j => (ν j : ℤ)) i ((ν i : ℤ) + 1)))
          (sX N fun j => (μ j : ℤ)) = 0 := by
      intro i hik
      cases ha : IsAddable ν i
      · rw [sX_addBox_eq_zero hνa ha]
        simp [fischer]
      · rw [← cast_addBox]
        refine fischer_sX_eq_zero_of_eig T hadj (heig _ (addBox_antitone hνa ha)) (heig μ hμ) ?_
        rw [← he, hlamν, casEig_addBox, casEig_addBox]
        intro h
        exact hik (content_injective hνa (by linarith))
    have hlamterm : fischer (sX N fun i => (lam i : ℤ)) (sX N fun j => (μ j : ℤ))
        = fischer (trX N * sX N fun i => (ν i : ℤ)) (sX N fun j => (μ j : ℤ)) := by
      rw [hpieri, fischer_sum_left, Fintype.sum_eq_single k hother, ← cast_addBox, ← hlamν]
    rw [hlamterm, fischer_trX_mul_sX]
    -- each removal from `μ`, by induction
    have hrem : ∀ j : Fin (l + 1),
        fischer (sX N fun i => (ν i : ℤ)) (sX N (Function.update (fun i => (μ i : ℤ)) j ((μ j : ℤ) - 1)))
          = if 0 < μ j ∧ removeBox μ j = ν then wQ N ν else 0 := by
      intro j
      cases hc : IsCorner μ j
      · rw [sX_removeBox_eq_zero hμ hc, fischer_zero_right, if_neg]
        rintro ⟨hpos, hrm⟩
        have := corner_of_antitone_removeBox hpos (hrm ▸ hνa)
        rw [hc] at this
        exact Bool.false_ne_true this
      · obtain ⟨hμa, hjpos⟩ := removeBox_antitone hμ hc
        rw [← cast_removeBox hjpos, ih ν (removeBox μ j) hνa hμa hlast
          (by
            simp only [removeBox, Function.update_apply, hμlast]
            split_ifs with h
            · rw [← h, hμlast]
            · rfl) hsν
          (by have := sum_removeBox hjpos; omega)]
        by_cases hrm : removeBox μ j = ν
        · rw [if_pos hrm.symm, if_pos ⟨hjpos, hrm⟩]
        · rw [if_neg (Ne.symm hrm), if_neg fun h => hrm h.2]
    simp_rw [hrem]
    rw [Fintype.sum_eq_single k]
    · by_cases hμlam : lam = μ
      · subst hμlam
        rw [if_pos ⟨hkpos, rfl⟩, if_pos rfl, wQ_removeBox hkpos]
        push_cast [Nat.cast_sub hkpos]
        ring
      · rw [if_neg hμlam, if_neg, mul_zero]
        rintro ⟨hpos, hrm⟩
        apply hμlam
        rw [hlamν, ← hrm, addBox_removeBox hpos]
    · intro j hjk
      rw [if_neg, mul_zero]
      rintro ⟨hpos, hrm⟩
      apply hjk
      have hμν : μ = addBox ν j := by rw [← hrm, addBox_removeBox hpos]
      rw [hμν, hlamν, casEig_addBox, casEig_addBox] at he
      exact content_injective hνa (by linarith)

end Diagonal

/-! ## A zero row changes nothing -/

/-- `λ` with an empty row appended. -/
def padZero {l : ℕ} (lam : Fin l → ℕ) : Fin (l + 1) → ℕ :=
  fun i => if h : (i : ℕ) < l then lam ⟨i, h⟩ else 0

theorem padZero_castSucc {l : ℕ} (lam : Fin l → ℕ) (i : Fin l) : padZero lam i.castSucc = lam i := by
  simp [padZero]

theorem padZero_last {l : ℕ} (lam : Fin l → ℕ) : padZero lam (Fin.last l) = 0 := by
  simp [padZero]

theorem padZero_antitone {l : ℕ} {lam : Fin l → ℕ} (h : Antitone lam) : Antitone (padZero lam) := by
  intro a b hab
  simp only [padZero]
  split_ifs with hb ha
  · exact h (show (⟨a, ha⟩ : Fin l) ≤ ⟨b, hb⟩ from Fin.le_def.mpr (Fin.le_def.mp hab))
  · exact absurd (lt_of_le_of_lt (Fin.le_def.mp hab) hb) ha
  · exact Nat.zero_le _
  · exact le_rfl

theorem sum_padZero {l : ℕ} (lam : Fin l → ℕ) : ∑ i, padZero lam i = ∑ i, lam i := by
  rw [Fin.sum_univ_castSucc, padZero_last, add_zero]
  simp_rw [padZero_castSucc]

theorem padZero_injective {l : ℕ} : Function.Injective (padZero (l := l)) := by
  intro lam mu h
  funext i
  have := congr_fun h i.castSucc
  rwa [padZero_castSucc, padZero_castSucc] at this

theorem wQ_padZero {l : ℕ} (lam : Fin l → ℕ) : wQ N (padZero lam) = wQ N lam := by
  rw [wQ, Fin.prod_univ_castSucc, padZero_last, range_zero, prod_empty, mul_one]
  simp_rw [padZero_castSucc]
  rfl

/-- **An empty row does not change `s_λ(X)`**: the last row of the Jacobi–Trudi matrix is a unit
vector. -/
theorem sX_padZero {l : ℕ} (lam : Fin l → ℕ) :
    (sX N fun i => (padZero lam i : ℤ)) = sX N fun i => (lam i : ℤ) := by
  classical
  rw [sX, Matrix.det_succ_row _ (Fin.last l), sum_eq_single (Fin.last l)]
  · have hl : ((padZero lam (Fin.last l) : ℕ) : ℤ) = 0 := by simp [padZero_last]
    simp only [Matrix.of_apply]
    rw [jt_last_row (fun i => (padZero lam i : ℤ)) hl, Pi.single_eq_same, mul_one,
      Fin.succAbove_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, sX]
    congr 1
    ext i j
    simp [padZero_castSucc]
  · intro j _ hj
    have hl : ((padZero lam (Fin.last l) : ℕ) : ℤ) = 0 := by simp [padZero_last]
    simp only [Matrix.of_apply]
    rw [jt_last_row (fun i => (padZero lam i : ℤ)) hl, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · simp

/-- **The Fock diagonal for every shape, given a Casimir**: if `T` is Fock self-adjoint and
`T s_κ(X) = e(κ) s_κ(X)` for every partition `κ` with at most `l + 1` rows, then
`⟨s_λ(X), s_μ(X)⟩_Fock = δ_{λμ} ∏_{(i, c) ∈ λ} (N + c − i)` for all partitions `λ, μ` with `l`
rows and `|λ| = |μ|`. -/
theorem fischer_sX_sX_of_casimir
    (T : MvPolynomial (Fin N × Fin N) ℚ → MvPolynomial (Fin N × Fin N) ℚ) {l : ℕ}
    (hadj : ∀ f g, fischer (T f) g = fischer f (T g))
    (heig : ∀ ν : Fin (l + 1) → ℕ, Antitone ν →
      T (sX N fun i => (ν i : ℤ)) = casEig N ν • sX N fun i => (ν i : ℤ))
    {lam mu : Fin l → ℕ} (hlam : Antitone lam) (hmu : Antitone mu)
    (hs : ∑ i, lam i = ∑ i, mu i) :
    fischer (sX N fun i => (lam i : ℤ)) (sX N fun i => (mu i : ℤ))
      = if lam = mu then wQ N lam else 0 := by
  have h := fischer_sX_sX_of_casimir_aux T hadj heig (∑ i, lam i) (padZero lam) (padZero mu)
    (padZero_antitone hlam) (padZero_antitone hmu) (padZero_last lam) (padZero_last mu)
    (sum_padZero lam) (by rw [sum_padZero, hs])
  rw [sX_padZero, sX_padZero, wQ_padZero] at h
  rw [h]
  exact if_congr padZero_injective.eq_iff rfl rfl

/-- **The Fock diagonal for every shape, from the eigenvalue of the Casimir**: if
`C s_κ(X) = e(κ) s_κ(X)` for every partition `κ` with at most `l + 1` rows, then
`⟨s_λ(X), s_μ(X)⟩_Fock = δ_{λμ} ∏_{(i, c) ∈ λ} (N + c − i)` for all partitions `λ, μ` with `l`
rows and `|λ| = |μ|`. The self-adjointness of `C` is proved (`fischer_cas`); the eigenvalue is
the only hypothesis. -/
theorem fischer_sX_sX_of_cas {l : ℕ}
    (heig : ∀ ν : Fin (l + 1) → ℕ, Antitone ν →
      cas N (sX N fun i => (ν i : ℤ)) = casEig N ν • sX N fun i => (ν i : ℤ))
    {lam mu : Fin l → ℕ} (hlam : Antitone lam) (hmu : Antitone mu)
    (hs : ∑ i, lam i = ∑ i, mu i) :
    fischer (sX N fun i => (lam i : ℤ)) (sX N fun i => (mu i : ℤ))
      = if lam = mu then wQ N lam else 0 :=
  fischer_sX_sX_of_casimir (cas N) fischer_cas heig hlam hmu hs

end RMT.Fock
