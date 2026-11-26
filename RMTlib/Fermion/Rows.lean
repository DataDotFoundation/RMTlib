import RMTlib.Fermion.Maya
import RMTlib.Symmetric.Corners

/-!
# Rows and Maya diagrams: charge sectors

A partition with at most `N` rows, `ν : Fin N → ℕ` antitone, and a charge `n ∈ ℤ` give the Maya
diagram `ofRows n ν` whose occupied sites are the shifted Maya positions
`b_i + n = ν_i − i − 1 + n` (`i < N`) together with the sea `{b < n − N}`. This is the Maya
diagram of `RMT.Symmetric.Corners` (`Corners.maya`), shifted by the charge.

## Main results

* `occ_ofRows`, `charge_ofRows`, `energy_ofRows`: `ofRows n ν` has charge `n` and energy
  `|ν| + n(n − 1)/2` (`tri n`).
* `corners_charge_eq`: **compatibility with `Corners.charge`.** The corner charge is the discrete
  derivative of the occupation: `Corners.charge ν u = 𝟙[u − 1 occupied] − 𝟙[u occupied]` for
  `ofRows 0 ν`. The external charge `+1` at `−N` is the edge of the Dirac sea.
* `rowsEquiv N n`: antitone `ν : Fin N → ℕ` ≃ Maya diagrams of charge `n` whose sites below
  `n − N` are all occupied.
* `sectorEquiv n k`: antitone `ν : Fin k → ℕ` with `|ν| = k` ≃ Maya diagrams of charge `n` and
  energy `k + n(n − 1)/2`. **This is the boson–fermion correspondence in one charge sector and one
  degree.**
* `partitionEquiv k`: Mathlib's `Nat.Partition k` ≃ antitone `ν : Fin k → ℕ` with `|ν| = k`.
* `mayaEquiv`: **the boson–fermion correspondence**, `Maya ≃ Σ (n : ℤ), Σ (k : ℕ), Nat.Partition k`,
  with `charge = n` and `energy = k + tri n` (`charge_mayaEquiv`, `energy_mayaEquiv`).
* `tri_charge_le_energy`: every Maya diagram has energy at least `n(n − 1)/2`, its charge energy.
-/

open Finset

namespace RMT.Fermion

open Maya
open RMT.Symmetric.Corners (maya mayaSet maya_strictAnti maya_injective)

/-- The charge energy `n(n − 1)/2`, the energy of the vacuum of charge `n`. -/
def tri (n : ℤ) : ℕ := (n * (n - 1) / 2).toNat

theorem two_mul_tri (n : ℤ) : 2 * (tri n : ℤ) = n * (n - 1) := by
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  have h0 : 0 ≤ n * (n - 1) := by
    rcases le_or_gt 0 n with h | h
    · rcases eq_or_lt_of_le h with rfl | h
      · simp
      · exact mul_nonneg h.le (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos h.le (by omega)
  unfold tri
  rw [hm] at h0 ⊢
  omega

variable {N : ℕ}

/-- The occupied sites of the rows: `b_i + n = ν_i − i − 1 + n`. -/
def rowSites (n : ℤ) (ν : Fin N → ℕ) : Finset ℤ := univ.image fun i => maya ν i + n

theorem le_of_mem_rowSites {n : ℤ} {ν : Fin N → ℕ} {b : ℤ} (hb : b ∈ rowSites n ν) :
    n - N ≤ b := by
  obtain ⟨i, -, rfl⟩ := mem_image.mp hb
  have := i.isLt; unfold maya; omega

/-- **The Maya diagram of the rows `ν` in charge `n`**: occupied sites `ν_i − i − 1 + n` and the
sea `{b < n − N}`. -/
def ofRows (n : ℤ) (ν : Fin N → ℕ) : Maya where
  P := range (n - N).toNat ∪ ((rowSites n ν).filter (0 ≤ ·)).image Int.toNat
  H := (range (N - n).toNat).filter fun h => holeSite h ∉ rowSites n ν

theorem occ_ofRows (n : ℤ) (ν : Fin N → ℕ) (b : ℤ) :
    (ofRows n ν).occ b ↔ b ∈ rowSites n ν ∨ b < n - N := by
  rcases le_or_gt 0 b with hb | hb
  · rw [occ_of_nonneg _ hb]
    simp only [ofRows, mem_union, mem_range, mem_image, mem_filter]
    constructor
    · rintro (h | ⟨x, ⟨hx, hx0⟩, hxb⟩)
      · right; omega
      · left; rwa [show b = x by omega]
    · rintro (h | h)
      · exact Or.inr ⟨b, ⟨h, hb⟩, rfl⟩
      · left; omega
  · rw [occ_of_neg _ hb]
    have hs : holeSite (-b - 1).toNat = b := by unfold holeSite; omega
    simp only [ofRows, mem_filter, mem_range, hs, not_and, not_not]
    constructor
    · intro h
      by_cases h' : b < n - N
      · exact Or.inr h'
      · exact Or.inl (h (by omega))
    · rintro (h | h) _
      · exact h
      · omega

/-- `[n − N, n + M)` is a window for `ofRows n ν` when `ν ≤ M`. -/
theorem isWindow_ofRows (n : ℤ) {M : ℕ} {ν : Fin N → ℕ} (hM : ∀ i, ν i ≤ M) :
    (ofRows n ν).IsWindow (n - N) (n + M) := by
  refine ⟨fun b hb => (occ_ofRows n ν b).mpr (Or.inr hb), fun b hb h => ?_⟩
  rcases (occ_ofRows n ν b).mp h with h | h
  · obtain ⟨i, -, rfl⟩ := mem_image.mp h
    have := hM i; unfold maya at hb; omega
  · omega

theorem filter_occ_ofRows (n : ℤ) {M : ℕ} {ν : Fin N → ℕ} (hM : ∀ i, ν i ≤ M) :
    (Ico (n - N) (n + M)).filter (ofRows n ν).occ = rowSites n ν := by
  ext b
  simp only [mem_filter, mem_Ico, occ_ofRows]
  constructor
  · rintro ⟨⟨h1, -⟩, h | h⟩
    · exact h
    · omega
  · intro h
    refine ⟨⟨le_of_mem_rowSites h, ?_⟩, Or.inl h⟩
    obtain ⟨i, -, rfl⟩ := mem_image.mp h
    have := hM i; unfold maya; omega

theorem rowSites_card {ν : Fin N → ℕ} (hν : Antitone ν) (n : ℤ) : (rowSites n ν).card = N := by
  rw [rowSites, card_image_of_injective _ fun i j h => maya_injective hν (by simpa using h)]
  simp

/-- **One-body weights of rows**: `weight φ (ofRows n ν) = ∏_i φ(b_i + n) · seaWeight φ (n − N)`. -/
theorem weight_ofRows {G : Type*} [CommGroup G] (φ : ℤ → G) (n : ℤ) {ν : Fin N → ℕ}
    (hν : Antitone ν) :
    weight φ (ofRows n ν) = (∏ i, φ (maya ν i + n)) * seaWeight φ (n - N) := by
  have hM : ∀ i, ν i ≤ ∑ j, ν j := fun i => single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [weight_window φ (isWindow_ofRows n hM), filter_occ_ofRows n hM, rowSites,
    prod_image fun i _ j _ h => maya_injective hν (by simpa using h)]

/-- `ofRows n ν` has charge `n`. -/
theorem charge_ofRows (n : ℤ) {ν : Fin N → ℕ} (hν : Antitone ν) : (ofRows n ν).charge = n := by
  have hM : ∀ i, ν i ≤ ∑ j, ν j := fun i => single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [charge_window (isWindow_ofRows n hM), filter_occ_ofRows n hM, rowSites_card hν]
  ring

theorem two_mul_sum_fin (N : ℕ) : 2 * ∑ i : Fin N, ((i : ℤ) + 1) = N * (N + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℤ) + 1)]
  induction N with
  | zero => simp
  | succ k ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

/-- `2 · energy (ofRows n ν) = 2|ν| + n(n − 1)`. -/
theorem two_mul_energy_ofRows (n : ℤ) {ν : Fin N → ℕ} (hν : Antitone ν) :
    2 * ((ofRows n ν).energy : ℤ) = 2 * ∑ i, (ν i : ℤ) + n * (n - 1) := by
  have hM : ∀ i, ν i ≤ ∑ j, ν j := fun i => single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [two_mul_energy_window (isWindow_ofRows n hM), filter_occ_ofRows n hM, rowSites,
    sum_image fun i _ j _ h => maya_injective hν (by simpa using h)]
  have h := two_mul_sum_fin N
  have e : ∑ i : Fin N, (maya ν i + n) = ∑ i, (ν i : ℤ) - ∑ i : Fin N, ((i : ℤ) + 1) + N * n := by
    rw [show ∑ i : Fin N, (maya ν i + n) = ∑ i : Fin N, ((ν i : ℤ) - ((i : ℤ) + 1) + n) from
      sum_congr rfl fun i _ => by unfold maya; ring, sum_add_distrib, sum_sub_distrib]
    simp
  rw [e]
  linear_combination (-1 : ℤ) * h

/-- **The energy of rows**: `energy (ofRows n ν) = |ν| + n(n − 1)/2`. -/
theorem energy_ofRows (n : ℤ) {ν : Fin N → ℕ} (hν : Antitone ν) :
    (ofRows n ν).energy = ∑ i, ν i + tri n := by
  have h := two_mul_energy_ofRows n hν
  have h2 := two_mul_tri n
  have : ((ofRows n ν).energy : ℤ) = ∑ i, (ν i : ℤ) + tri n := by linarith
  exact_mod_cast this

/-! ## Compatibility with `Corners.charge` -/

/-- **The corner charge is the discrete derivative of the occupation.** For `ofRows 0 ν`,
`Corners.charge ν u = 𝟙[u − 1 occupied] − 𝟙[u occupied]`; the external charge at `−N` is the edge
of the sea. -/
theorem corners_charge_eq (ν : Fin N → ℕ) (u : ℤ) :
    RMT.Symmetric.Corners.charge ν u =
      (if (ofRows 0 ν).occ (u - 1) then 1 else 0) - (if (ofRows 0 ν).occ u then 1 else 0) := by
  have hS : rowSites 0 ν = mayaSet ν := by simp [rowSites, mayaSet]
  have lo : ∀ b, b ∈ mayaSet ν → -(N : ℤ) ≤ b := fun b hb => by
    have := le_of_mem_rowSites (hS ▸ hb : b ∈ rowSites 0 ν); omega
  simp only [RMT.Symmetric.Corners.charge, occ_ofRows, hS, zero_sub]
  rcases lt_trichotomy u (-(N : ℤ)) with h | h | h
  · have a : u - 1 ∉ mayaSet ν := fun hm => by have := lo _ hm; omega
    have b : u ∉ mayaSet ν := fun hm => by have := lo _ hm; omega
    simp [a, b, h, show u - 1 < -(N : ℤ) by omega, show u ≠ -(N : ℤ) by omega]
  · subst h
    have a : -(N : ℤ) - 1 ∉ mayaSet ν := fun hm => by have := lo _ hm; omega
    by_cases b : -(N : ℤ) ∈ mayaSet ν <;> simp [a, b]
  · simp [show ¬ (u - 1 < -(N : ℤ)) by omega, show ¬ (u < -(N : ℤ)) by omega,
      show u ≠ -(N : ℤ) by omega]

/-! ## Rows ↔ Maya diagrams -/

theorem ofRows_injective (n : ℤ) {ν ν' : Fin N → ℕ} (hν : Antitone ν) (hν' : Antitone ν')
    (h : ofRows n ν = ofRows n ν') : ν = ν' := by
  have hS : rowSites n ν = rowSites n ν' := by
    ext b
    constructor
    · intro hb
      have := (occ_ofRows n ν b).mpr (Or.inl hb)
      rw [h, occ_ofRows] at this
      rcases this with h' | h'
      · exact h'
      · exact absurd (le_of_mem_rowSites hb) (not_le.mpr h')
    · intro hb
      have := (occ_ofRows n ν' b).mpr (Or.inl hb)
      rw [← h, occ_ofRows] at this
      rcases this with h' | h'
      · exact h'
      · exact absurd (le_of_mem_rowSites hb) (not_le.mpr h')
  have anti : ∀ μ : Fin N → ℕ, Antitone μ → StrictAnti fun i => maya μ i + n :=
    fun μ hμ i j hij => by
      have := maya_strictAnti hμ hij
      show maya μ j + n < maya μ i + n
      omega
  have hr : Set.range (fun i => maya ν i + n) = Set.range (fun i => maya ν' i + n) := by
    have := congrArg (fun s : Finset ℤ => (s : Set ℤ)) hS
    simpa [rowSites] using this
  have hf := ((anti ν hν).range_inj_of_wellFoundedGT (anti ν' hν')).mp hr
  funext i
  have := congrFun hf i
  unfold maya at this; omega

/-- A strictly increasing `Fin N → ℤ` grows by at least one per step. -/
theorem StrictMono.add_le_fin {e : Fin N → ℤ} (he : StrictMono e) (i j : Fin N) (hij : i ≤ j) :
    e i + ((j : ℤ) - i) ≤ e j := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (j : ℕ) = i + k := ⟨j - i, by have : (i : ℕ) ≤ j := hij; omega⟩
  induction k generalizing j with
  | zero =>
    have : j = i := Fin.ext (by omega)
    subst this; simp
  | succ k ih =>
    have hlt : (i : ℕ) + k < N := by have := j.isLt; omega
    have := ih ⟨i + k, hlt⟩ (by simp [Fin.le_def]) rfl
    have h2 := he (show (⟨i + k, hlt⟩ : Fin N) < j by simp [Fin.lt_def]; omega)
    simp only at this
    push_cast [hk] at this ⊢
    omega

/-- **Every Maya diagram of charge `n` with sea below `n − N` comes from `N` rows.** -/
theorem exists_ofRows {M : Maya} {n : ℤ} (hQ : M.charge = n) (hsea : ∀ b < n - N, M.occ b) :
    ∃ ν : Fin N → ℕ, Antitone ν ∧ ofRows n ν = M := by
  set B := max (n - N) M.top
  have hW : M.IsWindow (n - N) B :=
    ⟨hsea, fun b hb => M.not_occ_of_top_le (le_trans (le_max_right _ _) hb)⟩
  set F := (Ico (n - N) B).filter M.occ
  have hF : F.card = N := by
    have h := charge_window hW
    change M.charge = (F.card : ℤ) + _ at h
    omega
  set e := F.orderEmbOfFin hF
  have he_mem : ∀ j, e j ∈ F := fun j => orderEmbOfFin_mem F hF j
  have he_lo : ∀ j : Fin N, n - N + j ≤ e j := fun j => by
    have h0 : (0 : ℕ) < N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have h1 := StrictMono.add_le_fin e.strictMono ⟨0, h0⟩ j (by rw [Fin.le_def]; exact Nat.zero_le _)
    have h2 := (mem_Ico.mp (mem_filter.mp (he_mem ⟨0, h0⟩)).1).1
    simp only at h1; omega
  let ν : Fin N → ℕ := fun i => (e (Fin.rev i) - n + i + 1).toNat
  have hmaya : ∀ i, maya ν i + n = e (Fin.rev i) := fun i => by
    have := he_lo (Fin.rev i)
    simp only [Fin.val_rev] at this
    have hi := i.isLt
    simp only [maya, ν]
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    omega
  have hν : Antitone ν := by
    intro i i' hii'
    have := StrictMono.add_le_fin e.strictMono (Fin.rev i') (Fin.rev i) (Fin.rev_le_rev.mpr hii')
    have hi := i.isLt; have hi' := i'.isLt
    have hle : (i : ℕ) ≤ i' := hii'
    simp only [Fin.val_rev] at this
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at this
    push_cast at this
    simp only [ν]
    omega
  refine ⟨ν, hν, eq_of_occ fun b => ?_⟩
  rw [occ_ofRows]
  have hrows : rowSites n ν = F := by
    ext b
    simp only [rowSites, mem_image, mem_univ, true_and, hmaya]
    constructor
    · rintro ⟨i, rfl⟩; exact he_mem _
    · intro hb
      have : b ∈ Set.range e := by rw [range_orderEmbOfFin]; exact hb
      obtain ⟨j, rfl⟩ := this
      exact ⟨Fin.rev j, by simp⟩
  rw [hrows]
  constructor
  · rintro (h | h)
    · exact (mem_filter.mp h).2
    · exact hsea b h
  · intro h
    by_cases h' : b < n - N
    · exact Or.inr h'
    · left
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, ?_⟩, h⟩
      by_contra h''
      exact M.not_occ_of_top_le (le_trans (le_max_right _ _) (not_lt.mp h'')) h

/-- **Rows ↔ Maya diagrams**, at `N` rows and charge `n`. -/
noncomputable def rowsEquiv (N : ℕ) (n : ℤ) :
    {ν : Fin N → ℕ // Antitone ν} ≃ {M : Maya // M.charge = n ∧ ∀ b < n - N, M.occ b} :=
  Equiv.ofBijective
    (fun ν => ⟨ofRows n ν.1, charge_ofRows n ν.2,
      fun b hb => (occ_ofRows n ν.1 b).mpr (Or.inr hb)⟩)
    ⟨fun ν ν' h => Subtype.ext (ofRows_injective n ν.2 ν'.2 (congrArg Subtype.val h)),
      fun M => by
        obtain ⟨ν, hν, h⟩ := exists_ofRows M.2.1 M.2.2
        exact ⟨⟨ν, hν⟩, Subtype.ext h⟩⟩

/-! ## One charge sector, one degree -/

/-- An antitone `ν : Fin N → ℕ` of size `k` vanishes from row `k` on. -/
theorem eq_zero_of_sum {ν : Fin N → ℕ} (hν : Antitone ν) {k : ℕ} (hk : ∑ i, ν i = k)
    (i : Fin N) (hi : k ≤ i) : ν i = 0 := by
  by_contra h
  have h1 : ∀ j ∈ Iic i, 1 ≤ ν j := fun j hj => by
    have := hν (mem_Iic.mp hj); omega
  have h2 : ∑ j ∈ Iic i, 1 ≤ ∑ j ∈ Iic i, ν j := sum_le_sum h1
  have h3 : ∑ j ∈ Iic i, ν j ≤ ∑ j, ν j := sum_le_sum_of_subset (subset_univ _)
  simp only [sum_const, smul_eq_mul, mul_one, Fin.card_Iic] at h2
  omega

/-- Every Maya diagram is `ofRows` of some rows. -/
theorem exists_ofRows' (M : Maya) :
    ∃ (N : ℕ) (ν : Fin N → ℕ), Antitone ν ∧ ofRows M.charge ν = M := by
  refine ⟨(M.charge - M.bot).toNat, exists_ofRows rfl fun b hb => M.occ_of_lt_bot (by omega)⟩

/-- **The charge energy is a lower bound**: `energy M ≥ n(n − 1)/2`, `n = charge M`. -/
theorem tri_charge_le_energy (M : Maya) : tri M.charge ≤ M.energy := by
  obtain ⟨N, ν, hν, h⟩ := exists_ofRows' M
  have := energy_ofRows M.charge hν
  rw [h] at this; omega

/-- A Maya diagram of charge `n` and energy `k + tri n` has its sea below `n − k`. -/
theorem sea_of_energy {M : Maya} {n : ℤ} {k : ℕ} (hQ : M.charge = n)
    (hE : M.energy = k + tri n) : ∀ b < n - k, M.occ b := by
  obtain ⟨N, ν, hν, h⟩ := exists_ofRows' M
  rw [hQ] at h
  have hk : ∑ i, ν i = k := by
    have := energy_ofRows n hν; rw [h] at this; omega
  intro b hb
  rw [← h, occ_ofRows]
  by_cases h' : b < n - N
  · exact Or.inr h'
  · left
    have hi : (n - 1 - b).toNat < N := by omega
    refine mem_image.mpr ⟨⟨_, hi⟩, mem_univ _, ?_⟩
    have := eq_zero_of_sum hν hk ⟨_, hi⟩ (by simp only; omega)
    simp only [maya, this]
    omega

/-- **The boson–fermion correspondence in one charge sector and one degree**: antitone
`ν : Fin k → ℕ` of size `k` ≃ Maya diagrams of charge `n` and energy `k + n(n − 1)/2`. -/
noncomputable def sectorEquiv (n : ℤ) (k : ℕ) :
    {ν : Fin k → ℕ // Antitone ν ∧ ∑ i, ν i = k} ≃
      {M : Maya // M.charge = n ∧ M.energy = k + tri n} :=
  Equiv.ofBijective
    (fun ν => ⟨ofRows n ν.1, charge_ofRows n ν.2.1, by rw [energy_ofRows n ν.2.1, ν.2.2]⟩)
    ⟨fun ν ν' h => Subtype.ext (ofRows_injective n ν.2.1 ν'.2.1 (congrArg Subtype.val h)),
      fun M => by
        obtain ⟨ν, hν, h⟩ := exists_ofRows M.2.1 (sea_of_energy M.2.1 M.2.2)
        refine ⟨⟨ν, hν, ?_⟩, Subtype.ext h⟩
        have := energy_ofRows n hν
        rw [h, M.2.2] at this; omega⟩

theorem sectorEquiv_apply (n : ℤ) (k : ℕ) (ν : {ν : Fin k → ℕ // Antitone ν ∧ ∑ i, ν i = k}) :
    (sectorEquiv n k ν).1 = ofRows n ν.1 := rfl

/-! ## Mathlib's partitions -/

section Partition

/-- The rows of a partition: its parts in decreasing order, padded with zeros. -/
noncomputable def partRows {k : ℕ} (p : Nat.Partition k) (i : Fin k) : ℕ :=
  (p.parts.sort (· ≥ ·)).getD i 0

theorem sort_length_le {k : ℕ} (p : Nat.Partition k) : (p.parts.sort (· ≥ ·)).length ≤ k := by
  have h := List.length_le_sum_of_one_le (p.parts.sort (· ≥ ·)) fun i hi => by
    have : i ∈ p.parts := by rw [← Multiset.mem_coe, Multiset.sort_eq] at hi; exact hi
    exact p.parts_pos this
  have hs : (p.parts.sort (· ≥ ·)).sum = k := by
    rw [← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]
  omega

theorem ofFn_getD_eq {k : ℕ} (L : List ℕ) (hL : L.length ≤ k) :
    List.ofFn (fun i : Fin k => L.getD i 0) = L ++ List.replicate (k - L.length) 0 := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem_append]
    split_ifs with h
    · simp [h]
    · simp [List.getElem?_eq_none (by omega : L.length ≤ i)]

theorem ofFn_partRows {k : ℕ} (p : Nat.Partition k) :
    List.ofFn (partRows p) = p.parts.sort (· ≥ ·) ++
      List.replicate (k - (p.parts.sort (· ≥ ·)).length) 0 :=
  ofFn_getD_eq _ (sort_length_le p)

theorem partRows_antitone {k : ℕ} (p : Nat.Partition k) : Antitone (partRows p) := by
  rw [← List.sortedGE_ofFn_iff, List.sortedGE_iff_pairwise, ofFn_partRows, List.pairwise_append]
  refine ⟨Multiset.pairwise_sort _ _, ?_, fun a _ b hb => ?_⟩
  · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
  · rw [(List.mem_replicate.mp hb).2]; exact Nat.zero_le _

theorem partRows_sum {k : ℕ} (p : Nat.Partition k) : ∑ i, partRows p i = k := by
  rw [← List.sum_ofFn, ofFn_partRows, List.sum_append, List.sum_replicate, smul_zero, add_zero,
    ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]

theorem sum_filter_ne_zero (l : List ℕ) : (l.filter (· ≠ 0)).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons]
    by_cases ha : a = 0
    · rw [ite_eq_right (by simp [ha]), ih, List.sum_cons, ha, zero_add]
    · rw [ite_eq_left (by simp [ha]), List.sum_cons, List.sum_cons, ih]

/-- The partition with given rows: the nonzero rows. -/
def rowsPart {k : ℕ} (ν : Fin k → ℕ) (hν : ∑ i, ν i = k) : Nat.Partition k where
  parts := ((List.ofFn ν).filter (· ≠ 0) : List ℕ)
  parts_pos := fun {i} hi => by
    have := (List.mem_filter.mp (Multiset.mem_coe.mp hi)).2
    simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      at this
    omega
  parts_sum := by
    rw [Multiset.sum_coe, sum_filter_ne_zero, List.sum_ofFn, hν]

theorem rowsPart_partRows {k : ℕ} (p : Nat.Partition k) :
    rowsPart (partRows p) (partRows_sum p) = p := by
  apply Nat.Partition.ext
  simp only [rowsPart, ofFn_partRows, List.filter_append]
  have h1 : (p.parts.sort (· ≥ ·)).filter (· ≠ 0) = p.parts.sort (· ≥ ·) := by
    rw [List.filter_eq_self]
    intro a ha
    have : a ∈ p.parts := by rw [← Multiset.mem_coe, Multiset.sort_eq] at ha; exact ha
    have := p.parts_pos this
    simp; omega
  have h2 : (List.replicate (k - (p.parts.sort (· ≥ ·)).length) 0).filter (· ≠ 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp [(List.mem_replicate.mp ha).2]
  rw [h1, h2, List.append_nil, Multiset.sort_eq]

theorem partRows_rowsPart {k : ℕ} {ν : Fin k → ℕ} (hν : Antitone ν) (hs : ∑ i, ν i = k) :
    partRows (rowsPart ν hs) = ν := by
  apply List.ofFn_injective
  apply List.Perm.eq_of_sortedGE
  · exact List.sortedGE_ofFn_iff.mpr (partRows_antitone _)
  · exact List.sortedGE_ofFn_iff.mpr hν
  have hsort : ((rowsPart ν hs).parts.sort (· ≥ ·)).Perm ((List.ofFn ν).filter (· ≠ 0)) := by
    rw [← Multiset.coe_eq_coe, Multiset.sort_eq]; rfl
  have hzero : (List.ofFn ν).filter (fun x => !decide (x ≠ 0)) =
      List.replicate ((List.ofFn ν).filter (fun x => !decide (x ≠ 0))).length 0 := by
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun b hb => ?_⟩
    have := (List.mem_filter.mp hb).2
    simpa using this
  have hlen := List.length_eq_length_filter_add (l := List.ofFn ν) (fun x => decide (x ≠ 0))
  rw [List.length_ofFn] at hlen
  have hp := List.filter_append_perm (fun x => decide (x ≠ 0)) (List.ofFn ν)
  rw [ofFn_partRows, hsort.length_eq,
    show k - ((List.ofFn ν).filter (· ≠ 0)).length =
      ((List.ofFn ν).filter (fun x => !decide (x ≠ 0))).length by omega]
  refine List.Perm.trans ?_ hp
  refine List.Perm.append hsort ?_
  rw [← hzero]

/-- **Mathlib's partitions of `k` are the antitone `ν : Fin k → ℕ` of size `k`.** -/
noncomputable def partitionEquiv (k : ℕ) :
    Nat.Partition k ≃ {ν : Fin k → ℕ // Antitone ν ∧ ∑ i, ν i = k} where
  toFun p := ⟨partRows p, partRows_antitone p, partRows_sum p⟩
  invFun ν := rowsPart ν.1 ν.2.2
  left_inv p := rowsPart_partRows p
  right_inv ν := Subtype.ext (partRows_rowsPart ν.2.1 ν.2.2)

end Partition

/-- **The boson–fermion correspondence, degree by degree**: Maya diagrams of charge `n` and
energy `k + n(n − 1)/2` ≃ partitions of `k`. -/
noncomputable def sectorPartitionEquiv (n : ℤ) (k : ℕ) :
    Nat.Partition k ≃ {M : Maya // M.charge = n ∧ M.energy = k + tri n} :=
  (partitionEquiv k).trans (sectorEquiv n k)

/-- A charge sector, graded by the energy above the charge energy. -/
def chargeFiberEquiv (n : ℤ) :
    {M : Maya // M.charge = n} ≃ Σ k : ℕ, {M : Maya // M.charge = n ∧ M.energy = k + tri n} where
  toFun M := ⟨M.1.energy - tri n, M.1, M.2, by
    have := tri_charge_le_energy M.1; rw [M.2] at this; omega⟩
  invFun x := ⟨x.2.1, x.2.2.1⟩
  left_inv M := rfl
  right_inv := by
    rintro ⟨k, M, hQ, hE⟩
    have : M.energy - tri n = k := by omega
    subst this
    rfl

/-- **The boson–fermion correspondence**: a Maya diagram is a charge `n` and a partition `λ`, with
`energy = |λ| + n(n − 1)/2` (`charge_mayaEquiv`, `energy_mayaEquiv`). -/
noncomputable def mayaEquiv : (Σ (_ : ℤ) (k : ℕ), Nat.Partition k) ≃ Maya :=
  (Equiv.sigmaCongrRight fun n =>
    (Equiv.sigmaCongrRight fun k => sectorPartitionEquiv n k).trans (chargeFiberEquiv n).symm).trans
    (Equiv.sigmaFiberEquiv Maya.charge)

theorem charge_mayaEquiv (x : Σ (_ : ℤ) (k : ℕ), Nat.Partition k) :
    (mayaEquiv x).charge = x.1 := ((sectorPartitionEquiv x.1 x.2.1) x.2.2).2.1

theorem energy_mayaEquiv (x : Σ (_ : ℤ) (k : ℕ), Nat.Partition k) :
    (mayaEquiv x).energy = x.2.1 + tri x.1 := ((sectorPartitionEquiv x.1 x.2.1) x.2.2).2.2

end RMT.Fermion
