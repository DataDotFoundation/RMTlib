import RMTlib.Tableaux.MultisetHook.Bijection

/-!
# The Littlewood decomposition, on the abacus

Fix `r ≥ 1`. Cut the Maya diagram `M(λ)` into `r` runners, `M_ρ = {m : rm + ρ ∈ M(λ)}`
(`0 ≤ ρ < r`). Each runner is again a Maya diagram, hence a partition `λ^ρ` shifted by a charge
`c_ρ` (`quot`, `qcharge`, by `exists_of_maya`). This is the **`r`-quotient** of `λ`. Replacing each
runner by the vacuum of the same charge gives the **`r`-core** (`core`).

* `hooks_dvd`: **the hooks of `λ` divisible by `r` are `r` times the hooks of the quotient**,
  `{h ∈ H(λ) : r ∣ h} = ⊎_ρ r·H(λ^ρ)`. A hook `x − y` (particle `x`, hole `y`) is divisible
  by `r` exactly when `x` and `y` lie on the same runner.
* `sum_qcharge`: the runner charges add up to the charge of `λ`, which is `0` (window counting,
  `card_window`).
* `core_isTCore`, `littlewood`: `λ ↦ (core, quotient)` is a bijection from partitions onto
  `r`-cores × `r`-tuples of partitions.

In the language of the programme: the core is the zero mode (the charges), the quotient the
oscillators. The paper cites this decomposition (through Han–Ji, Theorem 15) rather than proving it.
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

open Classical

/-! ### Counting particles in a window -/

theorem occ_bot (z : ℤ) : Occ ⊥ z ↔ z < 0 := by
  constructor
  · rintro ⟨i, rfl⟩
    unfold site; have : (⊥ : YoungDiagram).rowLen i = 0 := by
      by_contra h
      exact YoungDiagram.notMem_bot (i, 0) (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
    rw [this]; push_cast; omega
  · intro h; exact ⟨(-z - 1).toNat, by
      unfold site; have : (⊥ : YoungDiagram).rowLen (-z - 1).toNat = 0 := by
        by_contra h'
        exact YoungDiagram.notMem_bot ((-z - 1).toNat, 0)
          (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      rw [this]; omega⟩

/-- **A partition has charge `0`**: in any window `[L, U]` reaching below `−ℓ(λ)` and above `λ₁`,
there are exactly `−L` particles. -/
theorem card_occ_window (μ : YoungDiagram) {L U : ℤ} (hL : L ≤ -(μ.colLen 0 : ℤ))
    (hU : (μ.rowLen 0 : ℤ) - 1 ≤ U) :
    (((Icc L U).filter (Occ μ)).card : ℤ) = -L := by
  have : ((Icc L U).filter (Occ μ)).card = (range (-L).toNat).card := by
    symm
    refine card_nbij (site μ) ?_ (fun i _ j _ h => (site_strictAnti μ).injective h) ?_
    · intro i hi
      rw [mem_coe, mem_range] at hi
      rw [mem_coe, mem_filter, mem_Icc]
      refine ⟨⟨?_, le_of_occ ⟨i, rfl⟩ |>.trans hU⟩, ⟨i, rfl⟩⟩
      by_cases h : i < μ.colLen 0
      · have : 0 < μ.rowLen i := μ.mem_iff_lt_rowLen.mp (μ.mem_iff_lt_colLen.mpr h)
        unfold site; omega
      · rw [site_of_ge μ (by omega)]; omega
    · intro x hx
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hx
      obtain ⟨⟨hxL, -⟩, i, rfl⟩ := hx
      refine ⟨i, ?_, rfl⟩
      simp only [coe_range, Set.mem_Iio]
      by_cases h : i < μ.colLen 0
      · omega
      · rw [site_of_ge μ (by omega)] at hxL; omega
  rw [this, card_range]; omega

/-- Counting a shifted Maya diagram in a window. -/
theorem card_window_shift (M : ℤ → Prop) (ν : YoungDiagram) (c : ℤ)
    (h : ∀ x, Occ ν x ↔ M (x + c)) {L U : ℤ} (hL : L - c ≤ -(ν.colLen 0 : ℤ))
    (hU : (ν.rowLen 0 : ℤ) - 1 ≤ U - c) :
    (((Icc L U).filter M).card : ℤ) = c - L := by
  have : ((Icc L U).filter M).card = ((Icc (L - c) (U - c)).filter (Occ ν)).card := by
    refine card_nbij' (· - c) (· + c) ?_ ?_ ?_ ?_
    · intro x hx; simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨⟨by omega, by omega⟩, (h _).mpr (by simpa using hx.2)⟩
    · intro x hx; simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨⟨by omega, by omega⟩, (h _).mp hx.2⟩
    · intro x _; simp
    · intro x _; simp
  rw [this, card_occ_window ν hL hU]; ring

/-- **A Maya diagram has a unique partition and charge.** -/
theorem maya_unique {M : ℤ → Prop} {ν ν' : YoungDiagram} {c c' : ℤ}
    (h : ∀ x, Occ ν x ↔ M (x + c)) (h' : ∀ x, Occ ν' x ↔ M (x + c')) : c = c' ∧ ν = ν' := by
  set L : ℤ := -(ν.colLen 0 : ℤ) - ν'.colLen 0 - |c| - |c'|
  set U : ℤ := ν.rowLen 0 + ν'.rowLen 0 + |c| + |c'|
  have h1 := card_window_shift M ν c h (L := L) (U := U) (by
    simp only [L]; have := abs_nonneg c'; have := neg_abs_le c; linarith) (by
    simp only [U]; have := abs_nonneg c'; have := le_abs_self c; linarith)
  have h2 := card_window_shift M ν' c' h' (L := L) (U := U) (by
    simp only [L]; have := abs_nonneg c; have := neg_abs_le c'; linarith) (by
    simp only [U]; have := abs_nonneg c; have := le_abs_self c'; linarith)
  have hc : c = c' := by linarith
  subst hc
  exact ⟨rfl, eq_of_occ fun x => (h x).trans (h' x).symm⟩

/-! ### Runners and the quotient -/

/-- Division by `r` on a runner. -/
theorem runner_divmod {r : ℕ} (hr : 0 < r) (m : ℤ) {ρ : ℕ} (hρ : ρ < r) :
    (r * m + ρ) / (r : ℤ) = m ∧ ((r * m + ρ) % (r : ℤ)).toNat = ρ := by
  have h := (Int.ediv_emod_unique (a := r * m + ρ) (b := r) (q := m) (r := ρ) (by omega)).mpr
    ⟨by ring, by omega, by omega⟩
  exact ⟨h.1, by rw [h.2]; simp⟩

/-- Every integer is on one runner. -/
theorem runner_decomp {r : ℕ} (hr : 0 < r) (x : ℤ) :
    x = r * (x / r) + ((x % r).toNat : ℕ) ∧ (x % r).toNat < r := by
  have h1 := Int.emod_nonneg x (by omega : (r : ℤ) ≠ 0)
  have h2 := emod_lt' hr x
  have h3 := Int.mul_ediv_add_emod x r
  exact ⟨by rw [Int.toNat_of_nonneg h1]; linarith, by omega⟩

/-- The runner `ρ` of `λ` is a Maya diagram. -/
theorem runner_exists {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) (ρ : ℕ) :
    ∃ ν : YoungDiagram, ∃ c : ℤ, ∀ m, Occ ν m ↔ Occ μ (r * (m + c) + ρ) := by
  obtain ⟨ν, c, h⟩ := exists_of_maya (fun m => Occ μ (r * m + ρ)) (-(μ.colLen 0 : ℤ) - ρ - 1)
    (μ.rowLen 0) (fun m hm => occ_of_lt (by
      have : (r : ℤ) * m ≤ m := by
        have : (1 : ℤ) ≤ r := by exact_mod_cast hr
        nlinarith
      omega)) (fun m hm => by
      have := le_of_occ hm
      rcases le_or_gt m 0 with h | h
      · omega
      · have : m ≤ (r : ℤ) * m := le_mul_of_one_le_left h.le (by exact_mod_cast hr)
        omega)
  exact ⟨ν, c, h⟩

/-- The `ρ`-th partition of the `r`-quotient. -/
def quot (r : ℕ) (μ : YoungDiagram) (ρ : ℕ) : YoungDiagram :=
  if h : 0 < r then Classical.choose (runner_exists h μ ρ) else ⊥

/-- The charge of the runner `ρ`. -/
def qcharge (r : ℕ) (μ : YoungDiagram) (ρ : ℕ) : ℤ :=
  if h : 0 < r then Classical.choose (Classical.choose_spec (runner_exists h μ ρ)) else 0

theorem quot_spec {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) (ρ : ℕ) (m : ℤ) :
    Occ (quot r μ ρ) m ↔ Occ μ (r * (m + qcharge r μ ρ) + ρ) := by
  unfold quot qcharge; rw [dite_eq_left hr, dite_eq_left hr]
  exact Classical.choose_spec (Classical.choose_spec (runner_exists hr μ ρ)) m

/-- The runner `ρ` of `λ` is the quotient partition shifted by its charge. -/
theorem runner_spec {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) (ρ : ℕ) (m : ℤ) :
    Occ μ (r * m + ρ) ↔ Occ (quot r μ ρ) (m - qcharge r μ ρ) := by
  rw [quot_spec hr, sub_add_cancel]

/-! ### Hooks divisible by `r` -/

/-- The sea, for any weight: sums over cells are sums over particle–hole pairs. -/
theorem sum_cells_eq_sum_pairs (μ : YoungDiagram) {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ c ∈ μ.cells, f (hook μ c) = ∑ p ∈ pairs μ, f (p.1 - p.2) := by
  refine sum_nbij (fun c => (site μ c.1, hole μ c.2)) ?_ ?_ ?_ (fun c _ => by rw [hook_eq])
  · intro c hc
    rw [YoungDiagram.mem_cells] at hc
    rw [mem_pairs]
    exact ⟨⟨c.1, rfl⟩, fun h => (occ_iff_not_hole μ _).mp h ⟨c.2, rfl⟩,
      (hole_lt_site_iff μ).mpr hc⟩
  · intro c _ c' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext ((site_strictAnti μ).injective h.1) ((hole_strictMono μ).injective h.2)
  · rintro ⟨x, y⟩ hp
    rw [mem_coe, mem_pairs] at hp
    obtain ⟨⟨i, rfl⟩, hy, hlt⟩ := hp
    obtain ⟨j, rfl⟩ := (cover μ y).resolve_left hy
    exact ⟨(i, j), by rw [mem_coe, YoungDiagram.mem_cells]; exact (hole_lt_site_iff μ).mp hlt, rfl⟩

theorem toDiv_hooks_map (μ : YoungDiagram) (f : ℤ → ℤ) :
    toDiv ((hooks μ).map f) = ∑ p ∈ pairs μ, pt (f (p.1 - p.2)) := by
  rw [hooks, Multiset.map_map, toDiv_map, ← sum_cells_eq_sum_pairs μ (fun h => pt (f h))]; rfl

theorem toDiv_hooks_filter (μ : YoungDiagram) (P : ℤ → Prop) [DecidablePred P] :
    toDiv ((hooks μ).filter P) = ∑ p ∈ (pairs μ).filter (fun p => P (p.1 - p.2)), pt (p.1 - p.2) := by
  rw [sum_filter, ← sum_cells_eq_sum_pairs μ (fun h => if P h then pt h else 0), ← sum_filter,
    hooks, Multiset.filter_map, toDiv_map]
  rfl

/-- **Littlewood: the hooks of `λ` divisible by `r` are `r` times the hooks of the quotient.** -/
theorem hooks_dvd {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) :
    (hooks μ).filter (fun h => (r : ℤ) ∣ h) =
      ∑ ρ ∈ range r, (hooks (quot r μ ρ)).map ((r : ℤ) * ·) := by
  apply toDiv_injective
  rw [toDiv_hooks_filter, toDiv_sum]
  simp only [toDiv_hooks_map]
  rw [← sum_sigma (range r) (fun ρ => pairs (quot r μ ρ))
    (fun x => pt ((r : ℤ) * (x.2.1 - x.2.2)))]
  have hT : (r : ℤ) ≠ 0 := by omega
  -- particle–hole pairs on one runner ↔ pairs of the quotient
  refine sum_nbij' (fun p => ⟨(p.1 % r).toNat, (p.1 / r - qcharge r μ (p.1 % r).toNat,
      p.2 / r - qcharge r μ (p.1 % r).toNat)⟩)
    (fun x => (r * (x.2.1 + qcharge r μ x.1) + x.1, r * (x.2.2 + qcharge r μ x.1) + x.1))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_pairs] at hp
    obtain ⟨⟨hx, hy, hlt⟩, hdvd⟩ := hp
    obtain ⟨hxd, hxr⟩ := runner_decomp hr x
    obtain ⟨hyd, -⟩ := runner_decomp hr y
    have hres : (y % r).toNat = (x % r).toNat := by
      rw [(emod_eq_iff (n := (r : ℤ))).mpr (by rw [← neg_sub]; exact (dvd_neg).mpr hdvd)]
    simp only [mem_sigma, mem_range, mem_pairs]
    refine ⟨hxr, ?_, ?_, ?_⟩
    · rw [quot_spec hr, sub_add_cancel, ← hxd]; exact hx
    · rw [quot_spec hr, sub_add_cancel, ← hres, ← hyd]; exact hy
    · rw [hres] at hyd
      have : (r : ℤ) * (y / r) < r * (x / r) := by linarith
      have := lt_of_mul_lt_mul_left this (by omega : (0 : ℤ) ≤ r)
      linarith
  · rintro ⟨ρ, z, w⟩ hx
    simp only [mem_sigma, mem_range, mem_pairs] at hx
    obtain ⟨hρ, hz, hw, hlt⟩ := hx
    simp only [mem_filter, mem_pairs]
    refine ⟨⟨(quot_spec hr μ ρ z).mp hz, fun h => hw ((quot_spec hr μ ρ w).mpr h), ?_⟩, ?_⟩
    · have : (r : ℤ) * (w + qcharge r μ ρ) < r * (z + qcharge r μ ρ) :=
        mul_lt_mul_of_pos_left (by linarith) (by omega)
      linarith
    · exact ⟨z - w, by ring⟩
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_pairs] at hp
    obtain ⟨-, hdvd⟩ := hp
    obtain ⟨hxd, -⟩ := runner_decomp hr x
    obtain ⟨hyd, -⟩ := runner_decomp hr y
    have hres : (y % r).toNat = (x % r).toNat := by
      rw [(emod_eq_iff (n := (r : ℤ))).mpr (by rw [← neg_sub]; exact (dvd_neg).mpr hdvd)]
    rw [hres] at hyd
    simp only [sub_add_cancel, Prod.mk.injEq]
    exact ⟨hxd.symm, hyd.symm⟩
  · rintro ⟨ρ, z, w⟩ hx
    simp only [mem_sigma, mem_range] at hx
    obtain ⟨hρ, -⟩ := hx
    obtain ⟨h1, h2⟩ := runner_divmod hr (z + qcharge r μ ρ) hρ
    obtain ⟨h3, -⟩ := runner_divmod hr (w + qcharge r μ ρ) hρ
    simp only
    rw [h2, h1, h3]
    simp
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_pairs] at hp
    obtain ⟨-, hdvd⟩ := hp
    obtain ⟨hxd, -⟩ := runner_decomp hr x
    obtain ⟨hyd, -⟩ := runner_decomp hr y
    have hres : (y % r).toNat = (x % r).toNat := by
      rw [(emod_eq_iff (n := (r : ℤ))).mpr (by rw [← neg_sub]; exact (dvd_neg).mpr hdvd)]
    rw [hres] at hyd
    congr 1
    conv_lhs => rw [hxd, hyd]
    ring

/-! ### The charges add up to zero -/

/-- **Counting by runners**: if each runner `ρ` of `M` is `Q ρ` shifted by `C ρ`, a window of
whole runner-blocks `[r m₀, r m₁ + r − 1]` contains `∑_ρ (C ρ − m₀)` points of `M`. -/
theorem card_window_runners {r : ℕ} (hr : 0 < r) (M : ℤ → Prop) (Q : ℕ → YoungDiagram)
    (C : ℕ → ℤ) (hM : ∀ ρ < r, ∀ m, M (r * m + ρ) ↔ Occ (Q ρ) (m - C ρ)) {m₀ m₁ : ℤ}
    (h₀ : ∀ ρ < r, m₀ - C ρ ≤ -((Q ρ).colLen 0 : ℤ))
    (h₁ : ∀ ρ < r, ((Q ρ).rowLen 0 : ℤ) - 1 ≤ m₁ - C ρ) :
    (((Icc (r * m₀) (r * m₁ + r - 1)).filter M).card : ℤ) = ∑ ρ ∈ range r, (C ρ - m₀) := by
  have hsplit : ((Icc (r * m₀) (r * m₁ + r - 1)).filter M).card =
      ((range r).sigma fun ρ => (Icc m₀ m₁).filter fun m => M (r * m + ρ)).card := by
    refine card_nbij' (fun x => ⟨(x % r).toNat, x / r⟩) (fun x => r * x.2 + x.1) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hx
      obtain ⟨hxd, hxr⟩ := runner_decomp hr x
      simp only [coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio, coe_filter, mem_Icc,
        Set.mem_ofPred_eq]
      refine ⟨hxr, ⟨?_, ?_⟩, by rw [← hxd]; exact hx.2⟩
      · by_contra h
        have := mul_le_mul_of_nonneg_left (show x / r ≤ m₀ - 1 by omega) (show (0 : ℤ) ≤ r by omega)
        have := mul_sub (r : ℤ) m₀ 1
        omega
      · by_contra h
        have := mul_le_mul_of_nonneg_left (show m₁ + 1 ≤ x / r by omega) (show (0 : ℤ) ≤ r by omega)
        have := mul_add (r : ℤ) m₁ 1
        omega
    · rintro ⟨ρ, m⟩ hx
      simp only [coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio, coe_filter, mem_Icc,
        Set.mem_ofPred_eq] at hx
      obtain ⟨hρ, ⟨h1, h2⟩, hm⟩ := hx
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq]
      refine ⟨⟨?_, ?_⟩, hm⟩
      · have : (r : ℤ) * m₀ ≤ r * m := mul_le_mul_of_nonneg_left h1 (by omega)
        omega
      · have : (r : ℤ) * m ≤ r * m₁ := mul_le_mul_of_nonneg_left h2 (by omega)
        omega
    · intro x _; simp only; exact (runner_decomp hr x).1.symm
    · rintro ⟨ρ, m⟩ hx
      simp only [coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio] at hx
      obtain ⟨h1, h2⟩ := runner_divmod hr m hx.1
      simp only [h1, h2]
  rw [hsplit, card_sigma, Nat.cast_sum]
  refine sum_congr rfl fun ρ hρ => ?_
  rw [mem_range] at hρ
  rw [card_window_shift (fun m => M (r * m + ρ)) (Q ρ) (C ρ) (fun x => by
    rw [hM ρ hρ, add_sub_cancel_right]) (by linarith [h₀ ρ hρ]) (by linarith [h₁ ρ hρ])]

/-- Window bounds for a family of partitions and charges. -/
theorem exists_window {r : ℕ} (Q : ℕ → YoungDiagram) (C : ℕ → ℤ) (K : ℤ) :
    ∃ m₀ m₁ : ℤ, m₀ ≤ -K ∧ K ≤ m₁ ∧ (∀ ρ < r, m₀ - C ρ ≤ -((Q ρ).colLen 0 : ℤ)) ∧
      ∀ ρ < r, ((Q ρ).rowLen 0 : ℤ) - 1 ≤ m₁ - C ρ := by
  set B : ℤ := ∑ ρ ∈ range r, (((Q ρ).colLen 0 : ℤ) + (Q ρ).rowLen 0 + |C ρ|) + |K|
  have hB : ∀ ρ < r, ((Q ρ).colLen 0 : ℤ) + (Q ρ).rowLen 0 + |C ρ| ≤ B := fun ρ hρ => by
    have := single_le_sum (f := fun ρ => ((Q ρ).colLen 0 : ℤ) + (Q ρ).rowLen 0 + |C ρ|)
      (fun _ _ => by positivity) (mem_range.mpr hρ)
    have := abs_nonneg K
    simp only [B]; linarith
  refine ⟨-B, B, ?_, ?_, fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · have := le_abs_self K; have : |K| ≤ B := by
      simp only [B]; have := sum_nonneg (s := range r)
        (f := fun ρ => ((Q ρ).colLen 0 : ℤ) + (Q ρ).rowLen 0 + |C ρ|) fun _ _ => by positivity
      linarith
    linarith
  · have := le_abs_self K; have : |K| ≤ B := by
      simp only [B]; have := sum_nonneg (s := range r)
        (f := fun ρ => ((Q ρ).colLen 0 : ℤ) + (Q ρ).rowLen 0 + |C ρ|) fun _ _ => by positivity
      linarith
    linarith
  · have := hB ρ hρ; have := neg_le_abs (C ρ); have : (0 : ℤ) ≤ (Q ρ).rowLen 0 := by positivity
    linarith
  · have := hB ρ hρ; have := le_abs_self (C ρ); have : (0 : ℤ) ≤ (Q ρ).colLen 0 := by positivity
    linarith

/-- **The runner charges add up to zero** (the charge of a partition). -/
theorem sum_qcharge {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) :
    ∑ ρ ∈ range r, qcharge r μ ρ = 0 := by
  obtain ⟨m₀, m₁, hK0, hK1, h₀, h₁⟩ := exists_window (r := r) (quot r μ) (qcharge r μ)
    (μ.colLen 0 + μ.rowLen 0)
  have e1 := card_window_runners hr (Occ μ) (quot r μ) (qcharge r μ)
    (fun ρ _ m => runner_spec hr μ ρ m) h₀ h₁
  have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hK : (0 : ℤ) ≤ μ.colLen 0 + μ.rowLen 0 := by positivity
  have e2 := card_occ_window μ (L := r * m₀) (U := r * m₁ + r - 1) (by
    have : (r : ℤ) * m₀ ≤ m₀ := by nlinarith
    have : (0 : ℤ) ≤ μ.rowLen 0 := by positivity
    omega) (by
    have : m₁ ≤ (r : ℤ) * m₁ := by nlinarith
    have : (0 : ℤ) ≤ μ.colLen 0 := by positivity
    omega)
  rw [e2, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at e1
  linarith

/-! ### The core and the bijection -/

/-- The core's Maya diagram: each runner replaced by the vacuum of the same charge. -/
def coreSet (r : ℕ) (μ : YoungDiagram) (x : ℤ) : Prop :=
  x / (r : ℤ) < qcharge r μ (x % r).toNat

theorem coreSet_runner {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) {ρ : ℕ} (hρ : ρ < r) (m : ℤ) :
    coreSet r μ (r * m + ρ) ↔ Occ ⊥ (m - qcharge r μ ρ) := by
  obtain ⟨h1, h2⟩ := runner_divmod hr m hρ
  rw [coreSet, h1, h2, occ_bot]; omega

/-- A diagram whose runners are each a shifted partition, with charges adding up to `0`, is the
diagram of a partition. -/
theorem exists_of_runners {r : ℕ} (hr : 0 < r) (M : ℤ → Prop) (Q : ℕ → YoungDiagram)
    (C : ℕ → ℤ) (hM : ∀ ρ < r, ∀ m, M (r * m + ρ) ↔ Occ (Q ρ) (m - C ρ))
    (hC : ∑ ρ ∈ range r, C ρ = 0) : ∃ ν : YoungDiagram, ∀ x, Occ ν x ↔ M x := by
  have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  obtain ⟨m₀, m₁, -, -, h₀, h₁⟩ := exists_window (r := r) Q C 0
  -- bounds on `M`
  have hM' : ∀ x, M x ↔ Occ (Q (x % r).toNat) (x / r - C (x % r).toNat) := fun x => by
    obtain ⟨hxd, hxr⟩ := runner_decomp hr x
    conv_lhs => rw [hxd]
    exact hM _ hxr _
  have hL : ∀ x < r * m₀, M x := by
    intro x hx
    obtain ⟨hxd, hxr⟩ := runner_decomp hr x
    rw [hM']
    apply occ_of_lt
    have := h₀ _ hxr
    have : x / (r : ℤ) < m₀ := by
      by_contra h; have : (r : ℤ) * m₀ ≤ r * (x / r) := mul_le_mul_of_nonneg_left (by omega)
        (by omega)
      omega
    omega
  have hU : ∀ x, M x → x ≤ r * m₁ + r - 1 := by
    intro x hx
    obtain ⟨hxd, hxr⟩ := runner_decomp hr x
    rw [hM'] at hx
    have := le_of_occ hx
    have := h₁ _ hxr
    have : x / (r : ℤ) ≤ m₁ := by omega
    have : (r : ℤ) * (x / r) ≤ r * m₁ := mul_le_mul_of_nonneg_left this (by omega)
    omega
  obtain ⟨ν, c, hν⟩ := exists_of_maya M (r * m₀) (r * m₁ + r - 1) hL hU
  -- the shift vanishes: count particles in the window
  obtain ⟨n₀, n₁, hn0, hn1, g₀, g₁⟩ := exists_window (r := r) Q C
    (|c| + ν.colLen 0 + ν.rowLen 0)
  have e1 := card_window_runners hr M Q C hM g₀ g₁
  have hc0 := abs_nonneg c
  have hrow : (0 : ℤ) ≤ ν.rowLen 0 := by positivity
  have hcol : (0 : ℤ) ≤ ν.colLen 0 := by positivity
  have e2 := card_window_shift M ν c hν (L := r * n₀) (U := r * n₁ + r - 1) (by
    have : (r : ℤ) * n₀ ≤ n₀ := by nlinarith
    have := neg_abs_le c; omega) (by
    have : n₁ ≤ (r : ℤ) * n₁ := by nlinarith
    have := le_abs_self c; omega)
  rw [e2, sum_sub_distrib, hC, sum_const, card_range, nsmul_eq_mul] at e1
  have hc : c = 0 := by linarith
  subst hc
  exact ⟨ν, fun x => by rw [hν, add_zero]⟩

/-- **The `r`-core of `λ`.** -/
def core (r : ℕ) (μ : YoungDiagram) : YoungDiagram :=
  if h : 0 < r then Classical.choose (exists_of_runners h (coreSet r μ) (fun _ => ⊥) (qcharge r μ)
    (fun _ hρ m => coreSet_runner h μ hρ m) (sum_qcharge h μ)) else ⊥

theorem core_spec {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) (x : ℤ) :
    Occ (core r μ) x ↔ coreSet r μ x := by
  unfold core; rw [dite_eq_left hr]
  exact Classical.choose_spec (exists_of_runners hr (coreSet r μ) (fun _ => ⊥) (qcharge r μ)
    (fun _ hρ m => coreSet_runner hr μ hρ m) (sum_qcharge hr μ)) x

/-- **The core is an `r`-core.** -/
theorem core_isTCore {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) : IsTCore r (core r μ) := by
  apply (coreStable hr _).mpr
  intro x hx
  rw [core_spec hr] at hx ⊢
  unfold coreSet at hx ⊢
  have e1 : (x - r) % (r : ℤ) = x % r := Int.sub_emod_right x r
  have e2 : (x - r) / (r : ℤ) = x / r - 1 := by
    rw [show x - r = x + r * (-1) by ring, Int.add_mul_ediv_left _ _ (by omega)]; ring
  rw [e1, e2]; omega

/-- A partition is determined by its runner charges and quotient. -/
theorem eq_of_runners {r : ℕ} (hr : 0 < r) {μ μ' : YoungDiagram}
    (hc : ∀ ρ < r, qcharge r μ ρ = qcharge r μ' ρ) (hq : ∀ ρ < r, quot r μ ρ = quot r μ' ρ) :
    μ = μ' := by
  apply eq_of_occ
  intro x
  obtain ⟨hxd, hxr⟩ := runner_decomp hr x
  rw [hxd, runner_spec hr, runner_spec hr, hc _ hxr, hq _ hxr]

/-- The core determines the runner charges. -/
theorem qcharge_eq_of_core {r : ℕ} (hr : 0 < r) {μ μ' : YoungDiagram}
    (h : core r μ = core r μ') (ρ : ℕ) (hρ : ρ < r) : qcharge r μ ρ = qcharge r μ' ρ := by
  have key : ∀ m, Occ ⊥ (m - qcharge r μ ρ) ↔ Occ ⊥ (m - qcharge r μ' ρ) := fun m => by
    rw [← coreSet_runner hr μ hρ, ← coreSet_runner hr μ' hρ, ← core_spec hr, ← core_spec hr, h]
  have h1 := key (qcharge r μ ρ); have h2 := key (qcharge r μ' ρ)
  simp only [occ_bot] at h1 h2
  omega


theorem eq_bot_of_hooks_eq_zero {ν : YoungDiagram} (h : hooks ν = 0) : ν = ⊥ := by
  have : ν.cells = ∅ := by
    rw [hooks, Multiset.map_eq_zero] at h
    exact Finset.val_eq_zero.mp h
  ext c; rw [this, YoungDiagram.cells_bot]

/-- **An `r`-core has an empty `r`-quotient.** -/
theorem quot_of_core {r : ℕ} (hr : 0 < r) {κ : YoungDiagram} (hκ : IsTCore r κ) (ρ : ℕ)
    (hρ : ρ < r) : quot r κ ρ = ⊥ := by
  have h := hooks_dvd hr κ
  have h0 : (hooks κ).filter (fun h => (r : ℤ) ∣ h) = 0 :=
    Multiset.filter_eq_nil.mpr fun h hh => hκ h hh
  rw [h0, eq_comm, sum_eq_zero_iff] at h
  exact eq_bot_of_hooks_eq_zero (Multiset.map_eq_zero.mp (h ρ (mem_range.mpr hρ)))

/-- **An `r`-core is its own core.** -/
theorem core_of_core {r : ℕ} (hr : 0 < r) {κ : YoungDiagram} (hκ : IsTCore r κ) :
    core r κ = κ := by
  apply eq_of_occ
  intro x
  obtain ⟨hxd, hxr⟩ := runner_decomp hr x
  rw [core_spec hr, hxd, coreSet_runner hr κ hxr, runner_spec hr, quot_of_core hr hκ _ hxr]

/-- **The Littlewood decomposition**: `λ ↦ (r-core, r-quotient)` is a bijection from partitions
onto pairs of an `r`-core and an `r`-tuple of partitions. -/
theorem littlewood {r : ℕ} (hr : 0 < r) (κ : YoungDiagram) (hκ : IsTCore r κ)
    (q : ℕ → YoungDiagram) : ∃! μ, core r μ = κ ∧ ∀ ρ < r, quot r μ ρ = q ρ := by
  -- build the Maya diagram runner by runner
  let M : ℤ → Prop := fun x => Occ (q (x % r).toNat) (x / r - qcharge r κ (x % r).toNat)
  have hM : ∀ ρ < r, ∀ m, M (r * m + ρ) ↔ Occ (q ρ) (m - qcharge r κ ρ) := by
    intro ρ hρ m
    obtain ⟨h1, h2⟩ := runner_divmod hr m hρ
    simp only [M, h1, h2]
  obtain ⟨μ, hμ⟩ := exists_of_runners hr M q (qcharge r κ) hM (sum_qcharge hr κ)
  have hrun : ∀ ρ < r, qcharge r μ ρ = qcharge r κ ρ ∧ quot r μ ρ = q ρ := by
    intro ρ hρ
    have h1 : ∀ m, Occ (quot r μ ρ) m ↔ (fun m => Occ μ (r * m + ρ)) (m + qcharge r μ ρ) :=
      quot_spec hr μ ρ
    have h2 : ∀ m, Occ (q ρ) m ↔ (fun m => Occ μ (r * m + ρ)) (m + qcharge r κ ρ) := fun m => by
      simp only; rw [hμ, hM ρ hρ, add_sub_cancel_right]
    exact maya_unique (M := fun m => Occ μ (r * m + ρ)) h1 h2
  have hcore : core r μ = κ := by
    rw [← core_of_core hr hκ]
    apply eq_of_occ
    intro x
    obtain ⟨hxd, hxr⟩ := runner_decomp hr x
    rw [core_spec hr, core_spec hr, hxd, coreSet_runner hr μ hxr, coreSet_runner hr κ hxr,
      (hrun _ hxr).1]
  refine ⟨μ, ⟨hcore, fun ρ hρ => (hrun ρ hρ).2⟩, ?_⟩
  rintro μ' ⟨hc', hq'⟩
  apply eq_of_runners hr
  · intro ρ hρ; exact qcharge_eq_of_core hr (hc'.trans hcore.symm) ρ hρ
  · intro ρ hρ; rw [hq' ρ hρ, (hrun ρ hρ).2]


/-! ### The size: `|λ| = |core| + r ∑_ρ |λ^ρ|` -/

theorem bot_rowLen (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 := by
  by_contra h
  exact YoungDiagram.notMem_bot (i, 0) (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))

theorem bot_colLen (j : ℕ) : (⊥ : YoungDiagram).colLen j = 0 := by
  by_contra h
  exact YoungDiagram.notMem_bot (0, j) (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))

/-- `|λ| = ∑_{i<K} λ_i` for `K ≥ ℓ(λ)`. -/
theorem card_cells_eq_sum_rowLen (μ : YoungDiagram) {K : ℕ} (hK : μ.colLen 0 ≤ K) :
    μ.cells.card = ∑ i ∈ range K, μ.rowLen i := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := range K)]
  · exact sum_congr rfl fun i _ => (μ.rowLen_eq_card).symm
  · intro c hc
    rw [mem_coe, YoungDiagram.mem_cells] at hc
    have : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) hc
    have := μ.mem_iff_lt_colLen.mp this
    rw [mem_coe, mem_range]; omega

/-- **The energy in a window**: `2|λ| = 2 ∑_{x ∈ M(λ) ∩ [A, U]} x + A(A − 1)` for `A ≤ −ℓ(λ)`,
`U ≥ λ₁ − 1`. -/
theorem two_mul_card_window (μ : YoungDiagram) {A U : ℤ} (hA : A ≤ -(μ.colLen 0 : ℤ))
    (hU : (μ.rowLen 0 : ℤ) - 1 ≤ U) :
    2 * (μ.cells.card : ℤ) = 2 * ∑ x ∈ (Icc A U).filter (Occ μ), x + A * (A - 1) := by
  have hsum : ∑ x ∈ (Icc A U).filter (Occ μ), x = ∑ i ∈ range (-A).toNat, site μ i := by
    symm
    refine sum_nbij (site μ) ?_ (fun i _ j _ h => (site_strictAnti μ).injective h) ?_
      (fun _ _ => rfl)
    · intro i hi
      rw [mem_range] at hi
      rw [mem_filter, mem_Icc]
      refine ⟨⟨?_, le_of_occ ⟨i, rfl⟩ |>.trans hU⟩, ⟨i, rfl⟩⟩
      by_cases h : i < μ.colLen 0
      · have : 0 < μ.rowLen i := μ.mem_iff_lt_rowLen.mp (μ.mem_iff_lt_colLen.mpr h)
        unfold site; omega
      · rw [site_of_ge μ (by omega)]; omega
    · intro x hx
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hx
      obtain ⟨⟨hxL, -⟩, i, rfl⟩ := hx
      refine ⟨i, ?_, rfl⟩
      simp only [coe_range, Set.mem_Iio]
      by_cases h : i < μ.colLen 0
      · omega
      · rw [site_of_ge μ (by omega)] at hxL; omega
  have hcard := card_cells_eq_sum_rowLen μ (K := (-A).toNat) (by omega)
  have hid := Finset.sum_range_id_mul_two ((-A).toNat + 1)
  rw [hsum]
  simp only [site, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [← Nat.cast_sum, ← hcard]
  have h2 : 2 * ∑ i ∈ range (-A).toNat, (i : ℤ) = (-A).toNat * ((-A).toNat - 1 : ℤ) := by
    have := Finset.sum_range_id_mul_two (-A).toNat
    rcases Nat.eq_zero_or_pos (-A).toNat with h0 | hpos
    · rw [h0]; simp
    have := congrArg (fun z : ℕ => (z : ℤ)) this; push_cast [Nat.cast_sub hpos] at this; linarith
  have hA' : ((-A).toNat : ℤ) = -A := by omega
  rw [hA'] at h2
  rw [hA']
  linarith

/-- The energy of a shifted Maya diagram in a window. -/
theorem two_mul_sum_window_shift (M : ℤ → Prop) (ν : YoungDiagram) (c : ℤ)
    (h : ∀ x, Occ ν x ↔ M (x + c)) {L U : ℤ} (hL : L - c ≤ -(ν.colLen 0 : ℤ))
    (hU : (ν.rowLen 0 : ℤ) - 1 ≤ U - c) :
    2 * ∑ x ∈ (Icc L U).filter M, x =
      2 * (ν.cells.card : ℤ) - (L - c) * (L - c - 1) + 2 * c * (c - L) := by
  have hcount := card_window_shift M ν c h hL hU
  have hshift : ∑ x ∈ (Icc L U).filter M, x = ∑ z ∈ (Icc (L - c) (U - c)).filter (Occ ν), (z + c) := by
    refine sum_nbij' (· - c) (· + c) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_filter, mem_Icc] at hx ⊢
      exact ⟨⟨by omega, by omega⟩, (h _).mpr (by simpa using hx.2)⟩
    · intro x hx; simp only [mem_filter, mem_Icc] at hx ⊢
      exact ⟨⟨by omega, by omega⟩, (h _).mp hx.2⟩
    · intro x _; simp
    · intro x _; simp
    · intro x _; simp
  have hcount' : ((Icc (L - c) (U - c)).filter (Occ ν)).card = ((Icc L U).filter M).card := by
    refine card_nbij' (· + c) (· - c) ?_ ?_ ?_ ?_
    · intro x hx; simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨⟨by omega, by omega⟩, (h _).mp hx.2⟩
    · intro x hx; simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨⟨by omega, by omega⟩, (h _).mpr (by simpa using hx.2)⟩
    · intro x _; simp
    · intro x _; simp
  rw [hshift, sum_add_distrib, sum_const, nsmul_eq_mul, hcount', hcount]
  have := two_mul_card_window ν hL hU
  linarith

/-- Sums over a window of whole runner-blocks, runner by runner. -/
theorem sum_window_runners {r : ℕ} (hr : 0 < r) (M : ℤ → Prop) (m₀ m₁ : ℤ) (f : ℤ → ℤ) :
    ∑ x ∈ (Icc (r * m₀) (r * m₁ + r - 1)).filter M, f x =
      ∑ ρ ∈ range r, ∑ m ∈ (Icc m₀ m₁).filter (fun m => M (r * m + ρ)), f (r * m + ρ) := by
  rw [← sum_sigma (range r) (fun ρ => (Icc m₀ m₁).filter fun m => M (r * m + ρ))
    (fun x => f (r * x.2 + x.1))]
  refine sum_nbij' (fun x => ⟨(x % r).toNat, x / r⟩) (fun x => r * x.2 + x.1) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_Icc] at hx
    obtain ⟨hxd, hxr⟩ := runner_decomp hr x
    simp only [mem_sigma, mem_range, mem_filter, mem_Icc]
    refine ⟨hxr, ⟨?_, ?_⟩, by rw [← hxd]; exact hx.2⟩
    · by_contra h
      have := mul_le_mul_of_nonneg_left (show x / r ≤ m₀ - 1 by omega) (show (0 : ℤ) ≤ r by omega)
      have := mul_sub (r : ℤ) m₀ 1
      omega
    · by_contra h
      have := mul_le_mul_of_nonneg_left (show m₁ + 1 ≤ x / r by omega) (show (0 : ℤ) ≤ r by omega)
      have := mul_add (r : ℤ) m₁ 1
      omega
  · rintro ⟨ρ, m⟩ hx
    simp only [mem_sigma, mem_range, mem_filter, mem_Icc] at hx
    obtain ⟨hρ, ⟨h1, h2⟩, hm⟩ := hx
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, hm⟩
    · have : (r : ℤ) * m₀ ≤ r * m := mul_le_mul_of_nonneg_left h1 (by omega)
      omega
    · have : (r : ℤ) * m ≤ r * m₁ := mul_le_mul_of_nonneg_left h2 (by omega)
      omega
  · intro x _; simp only; exact (runner_decomp hr x).1.symm
  · rintro ⟨ρ, m⟩ hx
    simp only [mem_sigma, mem_range] at hx
    obtain ⟨h1, h2⟩ := runner_divmod hr m hx.1
    simp only [h1, h2]
  · intro x _; simp only; rw [← (runner_decomp hr x).1]

/-- **The energy, runner by runner**: `2|λ|` in terms of the runners' partitions and charges. -/
theorem two_mul_card_runners {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) (Q : ℕ → YoungDiagram)
    (C : ℕ → ℤ) (hM : ∀ ρ < r, ∀ m, Occ μ (r * m + ρ) ↔ Occ (Q ρ) (m - C ρ)) {m₀ m₁ : ℤ}
    (h₀ : ∀ ρ < r, m₀ - C ρ ≤ -((Q ρ).colLen 0 : ℤ))
    (h₁ : ∀ ρ < r, ((Q ρ).rowLen 0 : ℤ) - 1 ≤ m₁ - C ρ)
    (hA : (r : ℤ) * m₀ ≤ -(μ.colLen 0 : ℤ)) (hU : (μ.rowLen 0 : ℤ) - 1 ≤ r * m₁ + r - 1) :
    2 * (μ.cells.card : ℤ) = ∑ ρ ∈ range r,
      ((r : ℤ) * (2 * ((Q ρ).cells.card : ℤ) - (m₀ - C ρ) * (m₀ - C ρ - 1) +
        2 * C ρ * (C ρ - m₀)) + 2 * ρ * (C ρ - m₀)) + r * m₀ * (r * m₀ - 1) := by
  rw [two_mul_card_window μ hA hU, sum_window_runners hr (Occ μ) m₀ m₁ (fun x => x), mul_sum]
  congr 1
  refine sum_congr rfl fun ρ hρ => ?_
  rw [mem_range] at hρ
  have hshift : ∀ x, Occ (Q ρ) x ↔ (fun m => Occ μ (r * m + ρ)) (x + C ρ) := fun x => by
    simp only; rw [hM ρ hρ, add_sub_cancel_right]
  have hS := two_mul_sum_window_shift (fun m => Occ μ (r * m + ρ)) (Q ρ) (C ρ) hshift
    (L := m₀) (U := m₁) (h₀ ρ hρ) (h₁ ρ hρ)
  have hN := card_window_shift (fun m => Occ μ (r * m + ρ)) (Q ρ) (C ρ) hshift
    (L := m₀) (U := m₁) (h₀ ρ hρ) (h₁ ρ hρ)
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hN]
  linear_combination (r : ℤ) * hS

/-- **The Littlewood size formula**: `|λ| = |core| + r ∑_ρ |λ^ρ|`. -/
theorem card_littlewood {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) :
    (μ.cells.card : ℤ) =
      (core r μ).cells.card + r * ∑ ρ ∈ range r, ((quot r μ ρ).cells.card : ℤ) := by
  have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  obtain ⟨m₀, m₁, hK0, hK1, h₀, h₁⟩ := exists_window (r := r) (quot r μ) (qcharge r μ)
    (μ.colLen 0 + μ.rowLen 0 + (core r μ).colLen 0 + (core r μ).rowLen 0)
  have hpos : (0 : ℤ) ≤ μ.colLen 0 + μ.rowLen 0 + (core r μ).colLen 0 + (core r μ).rowLen 0 := by
    positivity
  have hm0 : (r : ℤ) * m₀ ≤ m₀ := by nlinarith
  have hm1 : m₁ ≤ (r : ℤ) * m₁ := by nlinarith
  have hc0 : (0 : ℤ) ≤ (core r μ).colLen 0 := by positivity
  have hc1 : (0 : ℤ) ≤ (core r μ).rowLen 0 := by positivity
  have hμ0 : (0 : ℤ) ≤ μ.colLen 0 := by positivity
  have hμ1 : (0 : ℤ) ≤ μ.rowLen 0 := by positivity
  have e1 := two_mul_card_runners hr μ (quot r μ) (qcharge r μ)
    (fun ρ _ m => runner_spec hr μ ρ m) h₀ h₁ (by omega) (by omega)
  have e2 := two_mul_card_runners (m₀ := m₀) (m₁ := m₁) hr (core r μ) (fun _ => ⊥) (qcharge r μ)
    (fun ρ hρ m => by rw [core_spec hr]; exact coreSet_runner hr μ hρ m)
    (fun ρ hρ => by
      have := h₀ ρ hρ; have : (0 : ℤ) ≤ (quot r μ ρ).colLen 0 := by positivity
      rw [bot_colLen]; push_cast; linarith)
    (fun ρ hρ => by
      have := h₁ ρ hρ; have : (0 : ℤ) ≤ (quot r μ ρ).rowLen 0 := by positivity
      rw [bot_rowLen]; push_cast; linarith) (by omega) (by omega)
  have hdiff : ∑ ρ ∈ range r, ((r : ℤ) * (2 * ((quot r μ ρ).cells.card : ℤ) -
        (m₀ - qcharge r μ ρ) * (m₀ - qcharge r μ ρ - 1) + 2 * qcharge r μ ρ * (qcharge r μ ρ - m₀)) +
        2 * ρ * (qcharge r μ ρ - m₀)) -
      ∑ ρ ∈ range r, ((r : ℤ) * (2 * (((⊥ : YoungDiagram)).cells.card : ℤ) -
        (m₀ - qcharge r μ ρ) * (m₀ - qcharge r μ ρ - 1) + 2 * qcharge r μ ρ * (qcharge r μ ρ - m₀)) +
        2 * ρ * (qcharge r μ ρ - m₀)) =
      2 * r * ∑ ρ ∈ range r, ((quot r μ ρ).cells.card : ℤ) := by
    rw [← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun ρ _ => ?_
    rw [YoungDiagram.cells_bot, card_empty]; push_cast; ring
  linarith
end

end RMT.MultisetHook
