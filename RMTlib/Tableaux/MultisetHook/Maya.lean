import RMTlib.Tableaux.MultisetHook.Outline

/-!
# Proofs of the new statements: the Maya diagram of a `t`-core

This file proves the statements of `RMTlib.Tableaux.MultisetHook.Outline` and assembles the
paper's Theorem 1, minus bijectivity.

* `sea` (**N2**): the holes `j − λ'_j` are the complement of the sites `λ_i − i − 1`
  (`cover`, `occ_iff_not_hole`), and the cell `(i, j)` has hook `site i − hole j`, so the hooks
  are the particle–hole differences. This is the only step about the vacuum.
* `coreStable` (**N1**): a hook of length divisible by `t` is a particle with a hole `mt` below it.
* `complete`, `abacus` (**N3**): for a `t`-stable `M`, the occupied sites in a residue class are a
  ray ending at its `t`-maximal site, and the holes are the complementary ray. The particle–hole
  pairs of two runners `a, b ∈ V` are counted by `pairHooks (a − b)`.
* `folded` (**N5**) = N3 + the residue identity (N4).
* `charge` (**N6**): `∑_{a ∈ V} a` by comparing `M` with `M − t` in a window: the window
  contributes the vacuum value `−t(t + 1)/2`, and the `ℓ(λ)` particles above `−ℓ(λ)` contribute
  `t·ℓ(λ) − t·ℓ(λ) = 0`.
* `transposeV` (**N7**): `M(λᵀ) = −1 − (ℤ ∖ M(λ))`.
* `statement_of_bijective`: the paper's `Statement t`, given bijectivity of `φ_t` (proved in
  `RMTlib.Tableaux.MultisetHook.Bijection`).
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

open Classical

/-! ### Particles and holes -/

theorem site_succ_lt (μ : YoungDiagram) (i : ℕ) : site μ (i + 1) < site μ i := by
  have := μ.rowLen_anti i (i + 1) (by omega); unfold site; push_cast; omega

theorem site_strictAnti (μ : YoungDiagram) : StrictAnti (site μ) :=
  strictAnti_nat_of_succ_lt (site_succ_lt μ)

theorem hole_strictMono (μ : YoungDiagram) : StrictMono (hole μ) :=
  strictMono_nat_of_lt_succ fun j => by
    have := μ.colLen_anti j (j + 1) (by omega); unfold hole; push_cast; omega

/-- The cell `(i, j)` is in `λ` iff the hole of column `j` lies below the particle of row `i`. -/
theorem hole_lt_site_iff (μ : YoungDiagram) {i j : ℕ} : hole μ j < site μ i ↔ (i, j) ∈ μ := by
  have h1 := μ.mem_iff_lt_rowLen (i := i) (j := j)
  have h2 := μ.mem_iff_lt_colLen (i := i) (j := j)
  unfold hole site
  constructor
  · intro h; by_contra hn
    have a := mt h1.mpr hn; have b := mt h2.mpr hn; omega
  · intro hm; have := h1.mp hm; have := h2.mp hm; omega

theorem site_ne_hole (μ : YoungDiagram) (i j : ℕ) : site μ i ≠ hole μ j := by
  by_cases hm : (i, j) ∈ μ
  · exact ne_of_gt ((hole_lt_site_iff μ).mpr hm)
  · have a := mt (μ.mem_iff_lt_rowLen (i := i) (j := j)).mpr hm
    have b := mt (μ.mem_iff_lt_colLen (i := i) (j := j)).mpr hm
    unfold site hole; omega

theorem hook_eq (μ : YoungDiagram) (c : ℕ × ℕ) : hook μ c = site μ c.1 - hole μ c.2 := by
  unfold hook site hole; ring

theorem rowLen_eq_zero (μ : YoungDiagram) {i : ℕ} (h : μ.colLen 0 ≤ i) : μ.rowLen i = 0 := by
  by_contra hne
  have := μ.mem_iff_lt_colLen.mp (μ.mem_iff_lt_rowLen.mpr (show 0 < μ.rowLen i by omega))
  omega

theorem site_of_ge (μ : YoungDiagram) {i : ℕ} (h : μ.colLen 0 ≤ i) : site μ i = -i - 1 := by
  unfold site; rw [rowLen_eq_zero μ h]; simp

/-- **The sea, part 1**: every site is a particle or a hole. -/
theorem cover (μ : YoungDiagram) (z : ℤ) : Occ μ z ∨ ∃ j, hole μ j = z := by
  have hex : ∃ i, site μ i ≤ z :=
    ⟨μ.colLen 0 + (-z).toNat, by rw [site_of_ge μ (by omega)]; push_cast; omega⟩
  rcases (Nat.find_spec hex).lt_or_eq with hlt | heq
  · right
    set i0 := Nat.find hex
    have hmin : ∀ i < i0, z < site μ i := fun i hi => not_le.mp (Nat.find_min hex hi)
    have hz : 0 ≤ z + i0 := by unfold site at hlt; omega
    refine ⟨(z + i0).toNat, ?_⟩
    have hcol : μ.colLen (z + i0).toNat = i0 := by
      have hout : ¬ i0 < μ.colLen (z + i0).toNat := by
        rw [← μ.mem_iff_lt_colLen, μ.mem_iff_lt_rowLen]; unfold site at hlt; omega
      rcases Nat.eq_zero_or_pos i0 with h0 | hpos
      · omega
      · have hin : i0 - 1 < μ.colLen (z + i0).toNat := by
          rw [← μ.mem_iff_lt_colLen, μ.mem_iff_lt_rowLen]
          have := hmin (i0 - 1) (by omega); unfold site at this
          rw [Nat.cast_sub (by omega)] at this; push_cast at this; omega
        omega
    unfold hole; rw [hcol]; omega
  · left; exact ⟨_, heq⟩

/-- **The sea, part 2**: the holes are exactly the empty sites. -/
theorem occ_iff_not_hole (μ : YoungDiagram) (z : ℤ) : Occ μ z ↔ ¬ ∃ j, hole μ j = z := by
  constructor
  · rintro ⟨i, rfl⟩ ⟨j, hj⟩; exact site_ne_hole μ i j hj.symm
  · intro h; exact (cover μ z).resolve_right h

theorem le_of_occ {μ : YoungDiagram} {x : ℤ} (h : Occ μ x) : x ≤ μ.rowLen 0 - 1 := by
  obtain ⟨i, rfl⟩ := h
  have := (site_strictAnti μ).antitone (Nat.zero_le i)
  unfold site at this ⊢; simpa using this

theorem ge_of_not_occ {μ : YoungDiagram} {y : ℤ} (h : ¬ Occ μ y) : -(μ.colLen 0 : ℤ) ≤ y := by
  obtain ⟨j, rfl⟩ := (cover μ y).resolve_left h
  have := μ.colLen_anti 0 j (Nat.zero_le j)
  unfold hole; omega

theorem occ_of_lt {μ : YoungDiagram} {x : ℤ} (h : x < -(μ.colLen 0 : ℤ)) : Occ μ x := by
  by_contra hn; have := ge_of_not_occ hn; omega

/-! ### N2: the sea -/

theorem mem_pairs {μ : YoungDiagram} {p : ℤ × ℤ} :
    p ∈ pairs μ ↔ Occ μ p.1 ∧ ¬ Occ μ p.2 ∧ p.2 < p.1 := by
  unfold pairs
  simp only [mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2, h3⟩
    have := le_of_occ h1; have := ge_of_not_occ h2
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, h1, h2, h3⟩

/-- **N2.** -/
theorem sea (μ : YoungDiagram) : Sea μ := by
  refine ⟨occ_iff_not_hole μ, ?_⟩
  have e : toDiv (hooks μ) = ∑ c ∈ μ.cells, pt (hook μ c) := by rw [hooks, toDiv_map]; rfl
  rw [e]
  refine sum_nbij (fun c => (site μ c.1, hole μ c.2)) ?_ ?_ ?_ (fun c _ => by rw [hook_eq])
  · intro c hc
    rw [YoungDiagram.mem_cells] at hc
    rw [mem_pairs]
    refine ⟨⟨c.1, rfl⟩, fun h => (occ_iff_not_hole μ _).mp h ⟨c.2, rfl⟩, ?_⟩
    exact (hole_lt_site_iff μ).mpr hc
  · intro c _ c' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext ((site_strictAnti μ).injective h.1) ((hole_strictMono μ).injective h.2)
  · rintro ⟨x, y⟩ hp
    rw [mem_coe, mem_pairs] at hp
    obtain ⟨⟨i, rfl⟩, hy, hlt⟩ := hp
    obtain ⟨j, rfl⟩ := (cover μ y).resolve_left hy
    exact ⟨(i, j), by rw [mem_coe, YoungDiagram.mem_cells]; exact (hole_lt_site_iff μ).mp hlt, rfl⟩

/-! ### N1: cores are stable -/

/-- `t`-stability: `M − t ⊆ M`. -/
def Stable (t : ℕ) (μ : YoungDiagram) : Prop := ∀ x, Occ μ x → Occ μ (x - t)

theorem Stable.iter {t : ℕ} {μ : YoungDiagram} (hs : Stable t μ) (n : ℕ) {x : ℤ} (hx : Occ μ x) :
    Occ μ (x - t * n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih => have := hs _ ih; push_cast; rwa [show x - t * (n + 1) = x - t * n - t by ring]

theorem mem_hooks {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∈ μ) :
    site μ i - hole μ j ∈ hooks μ :=
  Multiset.mem_map.mpr ⟨(i, j), (YoungDiagram.mem_cells _).mpr h, hook_eq μ _⟩

/-- **N1.** -/
theorem coreStable {t : ℕ} (ht : 0 < t) (μ : YoungDiagram) : CoreStable t μ := by
  constructor
  · rintro hc x ⟨i, rfl⟩
    by_contra hn
    obtain ⟨j, hj⟩ := (cover μ _).resolve_left hn
    have hm : (i, j) ∈ μ := (hole_lt_site_iff μ).mp (by omega)
    exact hc _ (mem_hooks hm) (by rw [hj]; simp)
  · intro hs h hh hdvd
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hh
    rw [Finset.mem_val, YoungDiagram.mem_cells] at hc
    have hpos := (hole_lt_site_iff μ).mpr (show (c.1, c.2) ∈ μ from hc)
    rw [hook_eq] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : 0 ≤ m := by
      by_contra h0; have : (t : ℤ) * m < 0 := mul_neg_of_pos_of_neg (by omega) (by omega)
      omega
    have := Stable.iter (t := t) hs m.toNat ⟨c.1, rfl⟩
    rw [Int.toNat_of_nonneg hm0, ← hm, sub_sub_cancel] at this
    exact (occ_iff_not_hole μ _).mp this ⟨c.2, rfl⟩

theorem stable_of_core {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (h : IsTCore t μ) : Stable t μ :=
  (coreStable ht μ).mp h

/-! ### N3: the abacus of a stable diagram -/

theorem mem_vSet {t : ℕ} {μ : YoungDiagram} {x : ℤ} :
    x ∈ vSet t μ ↔ Occ μ x ∧ ¬ Occ μ (x + t) := by
  unfold vSet
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2⟩
    have := le_of_occ h1; have := ge_of_not_occ h2
    exact ⟨⟨by omega, by omega⟩, h1, h2⟩

/-- `2 ∑_{x ∈ [L − t, L)} x = 2tL − t(t + 1)`. -/
theorem two_mul_sum_Ico (L : ℤ) (t : ℕ) : 2 * ∑ x ∈ Ico (L - t) L, x = 2 * t * L - t * (t + 1) := by
  have e : ∑ x ∈ Ico (L - t) L, x = ∑ k ∈ range t, (L - 1 - k) := by
    refine sum_nbij' (fun x => (L - 1 - x).toNat) (fun k => L - 1 - k) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Ico] at hx; simp only [mem_range]; omega
    · intro k hk; simp only [mem_range] at hk; simp only [mem_Ico]; omega
    · intro x hx; simp only [mem_Ico] at hx; omega
    · intro k _; simp
    · intro x hx; simp only [mem_Ico] at hx; omega
  rw [e, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_sub]
  have := Finset.sum_range_id_mul_two t
  have h2 : 2 * ∑ k ∈ range t, (k : ℤ) = t * (t - 1 : ℤ) := by
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · simp
    have := congrArg (fun z : ℕ => (z : ℤ)) this; push_cast [Nat.cast_sub htp] at this; linarith
  rw [h2]; ring

section Stable

variable {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hs : Stable t μ)
include ht hs

/-- Particles: `x ∈ M` iff `x = a − t·k` for a `t`-maximal `a ∈ V` and `k ≥ 0`. -/
theorem occ_iff_vSet {x : ℤ} : Occ μ x ↔ ∃ a ∈ vSet t μ, ∃ k : ℕ, x = a - t * k := by
  constructor
  · intro hx
    have hex : ∃ n : ℕ, ¬ Occ μ (x + t * n) := by
      refine ⟨(μ.rowLen 0 - x).toNat + 1, fun h => ?_⟩
      have h1 := le_of_occ h
      have h2 : (((μ.rowLen 0 - x).toNat + 1 : ℕ) : ℤ) ≤ t * (((μ.rowLen 0 - x).toNat + 1 : ℕ) : ℤ) :=
        le_mul_of_one_le_left (by positivity) (by exact_mod_cast ht)
      have h3 : (((μ.rowLen 0 - x).toNat + 1 : ℕ) : ℤ) ≥ μ.rowLen 0 - x + 1 := by push_cast; omega
      omega
    have h0 : Nat.find hex ≠ 0 := fun h => by
      have := Nat.find_spec hex; rw [h] at this; simp at this; exact this hx
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hocc : Occ μ (x + t * k) := by
      have := Nat.find_min hex (show k < Nat.find hex by omega); push Not at this; exact this
    have hnot := Nat.find_spec hex
    rw [hk] at hnot
    refine ⟨x + t * k, mem_vSet.mpr ⟨hocc, ?_⟩, k, by ring⟩
    push_cast at hnot; rwa [show x + t * k + t = x + t * (k + 1) by ring]
  · rintro ⟨a, ha, k, rfl⟩; exact hs.iter k (mem_vSet.mp ha).1

/-- Holes: `y ∉ M` iff `y = b + t·l` for a `t`-maximal `b ∈ V` and `l ≥ 1`. -/
theorem not_occ_iff_vSet {y : ℤ} :
    ¬ Occ μ y ↔ ∃ b ∈ vSet t μ, ∃ l : ℕ, 1 ≤ l ∧ y = b + t * l := by
  constructor
  · intro hy
    have hex : ∃ n : ℕ, Occ μ (y - t * n) := by
      refine ⟨(y + μ.colLen 0).toNat + 1, occ_of_lt ?_⟩
      have h2 : (((y + μ.colLen 0).toNat + 1 : ℕ) : ℤ) ≤ t * (((y + μ.colLen 0).toNat + 1 : ℕ) : ℤ) :=
        le_mul_of_one_le_left (by positivity) (by exact_mod_cast ht)
      have h3 : (((y + μ.colLen 0).toNat + 1 : ℕ) : ℤ) ≥ y + μ.colLen 0 + 1 := by push_cast; omega
      omega
    have h0 : Nat.find hex ≠ 0 := fun h => by
      have := Nat.find_spec hex; rw [h] at this; simp at this; exact hy this
    obtain ⟨l, hl⟩ : ∃ l, Nat.find hex = l + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hnot : ¬ Occ μ (y - t * l) := Nat.find_min hex (show l < Nat.find hex by omega)
    have hocc := Nat.find_spec hex
    rw [hl] at hocc
    refine ⟨y - t * (l + 1 : ℕ), mem_vSet.mpr ⟨hocc, ?_⟩, l + 1, by omega, by ring⟩
    push_cast; rwa [show y - t * (l + 1) + t = y - t * l by ring]
  · rintro ⟨b, hb, l, hl, rfl⟩ h
    have := hs.iter (l - 1) h
    rw [show b + t * (l : ℤ) - t * ((l - 1 : ℕ) : ℤ) = b + t by push_cast [Nat.cast_sub hl]; ring]
      at this
    exact (mem_vSet.mp hb).2 this

/-- **N3, part 1**: the `t`-maximal sites form a complete residue system. -/
theorem complete : Complete t (vSet t μ) := by
  have inj : ∀ a ∈ vSet t μ, ∀ b ∈ vSet t μ, a % t = b % t → a = b := by
    intro a ha b hb h
    wlog hab : a ≤ b generalizing a b
    · exact (this b hb a ha h.symm (by omega)).symm
    obtain ⟨m, hm⟩ := emod_eq_iff.mp h.symm
    rcases hab.lt_or_eq with hlt | heq
    · exfalso
      have hm1 : 1 ≤ m := by
        by_contra h1; have : (t : ℤ) * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        omega
      have := hs.iter (m - 1).toNat (mem_vSet.mp hb).1
      rw [Int.toNat_of_nonneg (by omega), show b - t * (m - 1) = a + t by linarith] at this
      exact (mem_vSet.mp ha).2 this
    · exact heq
  refine ⟨inj, ?_⟩
  rw [← card_image_of_injOn (f := (· % (t : ℤ))) inj]
  have : (vSet t μ).image (· % (t : ℤ)) = (range t).image (fun n : ℕ => (n : ℤ)) := by
    ext r
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨a, -, rfl⟩
      have := emod_lt' ht a; have := Int.emod_nonneg a (by omega : (t : ℤ) ≠ 0)
      exact ⟨(a % t).toNat, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      have hz : Occ μ (n - t * (μ.colLen 0 + 1 : ℕ)) := occ_of_lt (by
        have h2 : ((μ.colLen 0 + 1 : ℕ) : ℤ) ≤ t * ((μ.colLen 0 + 1 : ℕ) : ℤ) :=
          le_mul_of_one_le_left (by positivity) (by exact_mod_cast ht)
        have h4 : (μ.colLen 0 : ℤ) ≤ t * (μ.colLen 0 : ℤ) :=
          le_mul_of_one_le_left (by positivity) (by exact_mod_cast ht)
        have h5 : (t : ℤ) * ((μ.colLen 0 + 1 : ℕ) : ℤ) = t * (μ.colLen 0 : ℤ) + t := by
          push_cast; ring
        omega)
      obtain ⟨a, ha, k, hk⟩ := (occ_iff_vSet ht hs).mp hz
      refine ⟨a, ha, ?_⟩
      have e1 : a = (n : ℤ) + t * ((k : ℤ) - (μ.colLen 0 + 1 : ℕ)) := by linarith
      rw [e1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [this, card_image_of_injective _ Nat.cast_injective, card_range]

/-- **N3, part 2**: the hook divisor is the sum of the pair divisors of the runners. -/
theorem hooks_eq_pairHooks :
    toDiv (hooks μ) = ∑ a ∈ vSet t μ, ∑ b ∈ vSet t μ, pairHooks t (a - b) := by
  have hV := complete ht hs
  rw [(sea μ).2]
  set V := vSet t μ
  -- the runners' pairs, indexed by `(a, b, n, j)`: hole `b + t(q − n)`, particle `a − t(n − j)`
  let T : Finset (Σ _ : ℤ × ℤ, Σ _ : ℕ, ℕ) :=
    (V ×ˢ V).sigma fun ab => (range (quo t (ab.1 - ab.2))).sigma fun n => range (n + 1)
  have hT : ∑ a ∈ V, ∑ b ∈ V, pairHooks t (a - b) =
      ∑ x ∈ T, pt ((x.1.1 - x.1.2) % t + t * x.2.2) := by
    rw [sum_sigma, ← sum_product']
    refine sum_congr rfl fun ab _ => ?_
    rw [sum_sigma, pairHooks]
    exact sum_congr rfl fun n _ => by rw [ray]
  rw [hT]
  have hq : ∀ a ∈ V, ∀ b ∈ V, 0 < quo t (a - b) →
      t ≤ a - b ∧ ((quo t (a - b) : ℕ) : ℤ) = (a - b) / t := by
    intro a _ b _ hpos
    unfold quo at hpos ⊢
    have h1 : 1 ≤ (a - b) / t := by omega
    have h2 := (Int.le_ediv_iff_mul_le (by omega : (0 : ℤ) < t)).mp h1
    exact ⟨by linarith, by omega⟩
  symm
  refine sum_bij (fun x _ => (x.1.1 - t * ((x.2.1 : ℤ) - x.2.2),
      x.1.2 + t * ((quo t (x.1.1 - x.1.2) : ℤ) - x.2.1))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, ⟨n, j⟩⟩ hx
    simp only [T, mem_sigma, mem_product, mem_range] at hx
    obtain ⟨⟨ha, hb⟩, hn, hj⟩ := hx
    obtain ⟨hab, hqd⟩ := hq a ha b hb (by omega)
    have hr := emod_pos_of_not_dvd' ht (hV.not_dvd ha hb (by omega))
    have hdiv := Int.emod_add_mul_ediv (a - b) t
    rw [mem_pairs]
    refine ⟨(occ_iff_vSet ht hs).mpr ⟨a, ha, n - j, by push_cast [Nat.cast_sub (by omega : j ≤ n)]; ring⟩,
      (not_occ_iff_vSet ht hs).mpr ⟨b, hb, quo t (a - b) - n, by omega,
        by push_cast [Nat.cast_sub (by omega : n ≤ quo t (a - b))]; ring⟩, ?_⟩
    simp only
    nlinarith
  · rintro ⟨⟨a, b⟩, ⟨n, j⟩⟩ hx ⟨⟨a', b'⟩, ⟨n', j'⟩⟩ hx' h
    simp only [T, mem_sigma, mem_product, mem_range] at hx hx'
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have ea : a = a' := hV.inj a hx.1.1 a' hx'.1.1 (emod_eq_iff.mpr
      ⟨((n : ℤ) - j) - (n' - j'), by linarith⟩)
    have eb : b = b' := hV.inj b hx.1.2 b' hx'.1.2 (emod_eq_iff.mpr
      ⟨(quo t (a' - b') - n' : ℤ) - (quo t (a - b) - n), by linarith⟩)
    subst ea eb
    have htz : (t : ℤ) ≠ 0 := by omega
    have e1 : ((n : ℤ) - j) = n' - j' := mul_left_cancel₀ htz (by linarith)
    have e2 : ((quo t (a - b) : ℤ) - n) = quo t (a - b) - n' := mul_left_cancel₀ htz (by linarith)
    have : n = n' := by omega
    have : j = j' := by omega
    subst_vars; rfl
  · rintro ⟨x, y⟩ hp
    rw [mem_pairs] at hp
    obtain ⟨hx, hy, hlt⟩ := hp
    obtain ⟨a, ha, k, rfl⟩ := (occ_iff_vSet ht hs).mp hx
    obtain ⟨b, hb, l, hl, rfl⟩ := (not_occ_iff_vSet ht hs).mp hy
    have hkl : ((k + l : ℕ) : ℤ) ≤ (a - b) / t := by
      rw [Int.le_ediv_iff_mul_le (by omega)]; push_cast; nlinarith
    have hq' : ((quo t (a - b) : ℕ) : ℤ) = (a - b) / t := by
      unfold quo; omega
    refine ⟨⟨(a, b), ⟨quo t (a - b) - l, quo t (a - b) - l - k⟩⟩, ?_, ?_⟩
    · simp only [T, mem_sigma, mem_product, mem_range]
      exact ⟨⟨ha, hb⟩, by omega, by omega⟩
    · simp only [Prod.mk.injEq]
      constructor
      · push_cast [Nat.cast_sub (show l ≤ quo t (a - b) by omega),
          Nat.cast_sub (show k ≤ quo t (a - b) - l by omega)]; ring
      · push_cast [Nat.cast_sub (show l ≤ quo t (a - b) by omega)]; ring
  · rintro ⟨⟨a, b⟩, ⟨n, j⟩⟩ hx
    simp only [T, mem_sigma, mem_product, mem_range] at hx
    obtain ⟨⟨ha, hb⟩, hn, hj⟩ := hx
    obtain ⟨-, hqd⟩ := hq a ha b hb (by omega)
    have hdiv := Int.emod_add_mul_ediv (a - b) t
    congr 1
    simp only
    rw [hqd]; linarith

/-- **N3.** -/
theorem abacus : Abacus t μ := ⟨complete ht hs, hooks_eq_pairHooks ht hs⟩

/-- **N5** (folded Eq. (2)) for stable diagrams: N3 + N4. -/
theorem folded : Folded t μ := folded_of_abacus ht (abacus ht hs)

/-! ### N6: the charge -/

/-- **N6** (the paper's Eq. (8)). -/
theorem charge : Charge t μ := by
  set L : ℤ := -(μ.colLen 0 : ℤ)
  set W := (Icc (L - t) (μ.rowLen 0 - 1)).filter (Occ μ)
  have hVW : vSet t μ = W.filter fun x => ¬ Occ μ (x + t) := by
    ext x; simp only [W, mem_filter, mem_Icc, mem_vSet]
    constructor
    · rintro ⟨h1, h2⟩
      have hu := le_of_occ h1; have hl := ge_of_not_occ h2
      exact ⟨⟨⟨by omega, hu⟩, h1⟩, h2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  have hsplit := sum_filter_add_sum_filter_not W (fun x => ¬ Occ μ (x + t)) id
  have hshift : ∑ x ∈ W.filter (fun x => ¬ ¬ Occ μ (x + t)), x =
      ∑ y ∈ W.filter (L ≤ ·), (y - t) := by
    refine sum_nbij' (· + t) (· - t) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [W, mem_filter, mem_Icc, not_not] at hx ⊢
      have := le_of_occ hx.2
      exact ⟨⟨⟨by omega, this⟩, hx.2⟩, by omega⟩
    · intro y hy
      simp only [W, mem_filter, mem_Icc, not_not] at hy ⊢
      refine ⟨⟨⟨by omega, by omega⟩, hs _ hy.1.2⟩, by simpa using hy.1.2⟩
    · intro x _; simp
    · intro y _; simp
    · intro x _; simp
  have hlow := sum_filter_add_sum_filter_not W (· < L) id
  have hIco : W.filter (· < L) = Ico (L - t) L := by
    ext x; simp only [W, mem_filter, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨⟨h1, by omega⟩, occ_of_lt h2⟩, h2⟩
  have hge : W.filter (fun x => ¬ x < L) = W.filter (L ≤ ·) := by
    ext x; simp only [mem_filter, not_lt]
  have hcard : (W.filter (L ≤ ·)).card = μ.colLen 0 := by
    symm
    rw [← card_range (μ.colLen 0)]
    refine card_nbij (site μ) ?_ (fun i _ j _ h => (site_strictAnti μ).injective h) ?_
    · intro i hi
      have hi : i < μ.colLen 0 := by simpa using hi
      have hrow : 0 < μ.rowLen i := μ.mem_iff_lt_rowLen.mp (μ.mem_iff_lt_colLen.mpr hi)
      have hu := le_of_occ (μ := μ) ⟨i, rfl⟩
      have hlo : L ≤ site μ i := by simp only [L]; unfold site; omega
      simp only [W, coe_filter, mem_filter, mem_Icc, Set.mem_ofPred_eq]
      exact ⟨⟨⟨by omega, hu⟩, ⟨i, rfl⟩⟩, hlo⟩
    · intro y hy
      simp only [W, coe_filter, mem_filter, mem_Icc, Set.mem_ofPred_eq] at hy
      obtain ⟨⟨-, i, rfl⟩, hL⟩ := hy
      refine ⟨i, ?_, rfl⟩
      simp only [coe_range, Set.mem_Iio]
      by_contra hi
      rw [site_of_ge μ (by omega)] at hL; omega
  have hshift' : ∑ x ∈ W.filter (fun x => ¬ ¬ Occ μ (x + t)), x =
      ∑ y ∈ W.filter (L ≤ ·), y - t * μ.colLen 0 := by
    rw [hshift, sum_sub_distrib, sum_const, hcard, nsmul_eq_mul]; ring
  have hlow' : ∑ x ∈ Ico (L - t) L, x + ∑ x ∈ W.filter (L ≤ ·), x = ∑ x ∈ W, x := by
    rw [← hIco, ← hge]; exact hlow
  have hI := two_mul_sum_Ico L t
  rw [Charge, hVW]
  have e : ∑ x ∈ W.filter (fun x => ¬ Occ μ (x + t)), x =
      ∑ x ∈ Ico (L - t) L, x + t * μ.colLen 0 := by
    simp only [id] at hsplit hlow'
    linarith
  rw [e, mul_add, hI]
  simp only [L]; ring

end Stable

/-! ### N7: conjugation -/

theorem occ_transpose (μ : YoungDiagram) (z : ℤ) : Occ μ.transpose z ↔ ¬ Occ μ (-1 - z) := by
  rw [occ_iff_not_hole μ, not_not]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, by unfold site hole; rw [YoungDiagram.rowLen_transpose]; ring⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by unfold site; rw [YoungDiagram.rowLen_transpose]; unfold hole at hi; omega⟩

/-- **N7.** -/
theorem transposeV (t : ℕ) (μ : YoungDiagram) : TransposeV t μ := by
  ext z
  rw [mem_vSet, occ_transpose, occ_transpose, mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨-1 - t - z, mem_vSet.mpr ⟨by rwa [not_not, show -1 - (z + t) = -1 - t - z by ring] at h2,
      by rwa [show -1 - (t : ℤ) - z + t = -1 - z by ring]⟩, by ring⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨h1, h2⟩ := mem_vSet.mp hb
    exact ⟨by rwa [show -1 - (-1 - (t : ℤ) - b) = b + t by ring],
      by rw [not_not, show -1 - (-1 - (t : ℤ) - b + t) = b by ring]; exact h1⟩

theorem Stable.transpose {t : ℕ} {μ : YoungDiagram} (hs : Stable t μ) : Stable t μ.transpose := by
  intro x hx
  rw [occ_transpose] at hx ⊢
  intro h; apply hx
  have := hs _ h
  rwa [show -1 - (x - t) - t = -1 - x by ring] at this

/-! ### Theorem 1, minus bijectivity -/

/-- **Dehaye–Han, Theorem 1**, all parts except the bijectivity of `φ_t`, which is taken as a
hypothesis. -/
theorem statement_of_bijective {t : ℕ} (ht : 0 < t)
    (hbij : ∀ v, IsVCoding t v → ∃! μ, IsTCore t μ ∧ vCoding t μ = v) : Statement t where
  coding _ hμ := coding_of_charge (complete ht (stable_of_core ht hμ))
    (charge ht (stable_of_core ht hμ))
  bijective := hbij
  size _ hμ := size_of_folded ht (complete ht (stable_of_core ht hμ))
    (folded ht (stable_of_core ht hμ)) (charge ht (stable_of_core ht hμ))
  divisor _ hμ := (divisor_iff_folded hμ (complete ht (stable_of_core ht hμ)).card).mpr
    (folded ht (stable_of_core ht hμ))
  transpose μ hμ := transpose_of (complete ht (stable_of_core ht hμ))
    (complete ht (stable_of_core ht hμ).transpose) (transposeV t μ)

/-- **Theorem 1 reduces to the bijectivity of `φ_t`.** -/
theorem theorem1_of_bijective
    (hbij : ∀ t, 0 < t → ∀ v, IsVCoding t v → ∃! μ, IsTCore t μ ∧ vCoding t μ = v) :
    Theorem1 := fun t ht => statement_of_bijective ht (hbij t ht)

end

end RMT.MultisetHook
