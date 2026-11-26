import Mathlib

/-!
# Maya diagrams: the fermionic Fock space

A **Maya diagram** is a set `S ⊆ ℤ` of occupied sites that differs from the **Dirac sea**
`{b < 0}` at finitely many sites. We record it by its finitely many defects: the particles
`P ⊆ ℕ` (occupied sites `p ≥ 0`) and the holes `H ⊆ ℕ` (the empty site `−h − 1 < 0` is the hole
`h`). So `Maya ≃ Finset ℕ × Finset ℕ`, and the sites live on `ℤ`, not on `ℤ + ½`.

## Conventions

The sites are those of `RMT.Symmetric.Corners`: the row `i` of a partition sits at the Maya
position `b_i = ν_i − i − 1`, so the empty partition is the sea `{b ≤ −1}` (see
`RMTlib/Fermion/Rows.lean`).

* `charge M = #P − #H`.
* `energy M = ∑_{p ∈ P} p + ∑_{h ∈ H} (h + 1)`: a particle at `b ≥ 0` costs `b`, a hole at `b < 0`
  costs `−b`. The vacuum of charge `n` (the sea `{b < n}`) has energy `n(n − 1)/2` (`tri n`), and
  in general `energy = |λ| + n(n − 1)/2` (`RMT.Fermion.energy_ofRows`). This is the `ℤ`-convention;
  in the `ℤ + ½` convention the charge energy would be `n²/2`.
* `weight φ M = ∏_{p ∈ P} φ(p) / ∏_{h ∈ H} φ(−h − 1)` for a **one-body potential** `φ : ℤ → G`
  (`G` a commutative group): the product of `φ` over the occupied sites, normalised against the
  sea. Charge and energy are the one-body weights of the potentials `1` and `b` (in
  `Multiplicative ℤ`): `weight_const`, `weight_ofAdd`.

## Main results

* `weight_window`: **the window formula.** If every site below `A` is occupied and every site from
  `B` on is empty, `weight φ M = ∏_{b ∈ [A, B), occupied} φ(b) · seaWeight φ A`, where
  `seaWeight φ A` is the weight of the vacuum `{b < A}` (`∏_{0 ≤ b < A} φ(b)`, or the inverse of
  `∏_{A ≤ b < 0} φ(b)`).
* `charge_window`, `two_mul_energy_window`: the special cases `charge = #{occupied in [A, B)} + A`
  and `2·energy = 2 ∑_{occupied in [A, B)} b + A(A − 1)`.
* `eq_of_occ`: a Maya diagram is determined by its occupied sites.
-/

open Finset

namespace RMT.Fermion

/-- **A Maya diagram**, by its defects relative to the Dirac sea `{b < 0}`: the particles `P`
(occupied sites `p ≥ 0`) and the holes `H` (the hole `h` is the empty site `−h − 1`). -/
@[ext]
structure Maya where
  /-- Particles: the occupied sites `p ≥ 0`. -/
  P : Finset ℕ
  /-- Holes: `h ∈ H` means the site `−h − 1 < 0` is empty. -/
  H : Finset ℕ
deriving DecidableEq

namespace Maya

/-- The site `−h − 1` of the hole `h`. -/
def holeSite (h : ℕ) : ℤ := -(h : ℤ) - 1

theorem holeSite_injective : Function.Injective holeSite := fun a b h => by
  unfold holeSite at h; omega

/-- **Occupation**: whether the site `b` is occupied. -/
def occ (M : Maya) (b : ℤ) : Prop := if 0 ≤ b then b.toNat ∈ M.P else (-b - 1).toNat ∉ M.H

instance (M : Maya) : DecidablePred M.occ := fun b => by unfold occ; infer_instance

theorem occ_of_nonneg (M : Maya) {b : ℤ} (hb : 0 ≤ b) : M.occ b ↔ b.toNat ∈ M.P := by
  simp [occ, hb]

theorem occ_of_neg (M : Maya) {b : ℤ} (hb : b < 0) : M.occ b ↔ (-b - 1).toNat ∉ M.H := by
  simp [occ, not_le.mpr hb]

theorem occ_natCast (M : Maya) (p : ℕ) : M.occ p ↔ p ∈ M.P := by
  rw [occ_of_nonneg M (by positivity)]; simp

theorem occ_holeSite (M : Maya) (h : ℕ) : M.occ (holeSite h) ↔ h ∉ M.H := by
  rw [occ_of_neg M (by unfold holeSite; omega)]
  have : (-holeSite h - 1).toNat = h := by unfold holeSite; omega
  rw [this]

/-- **A Maya diagram is determined by its occupied sites.** -/
theorem eq_of_occ {M M' : Maya} (h : ∀ b, M.occ b ↔ M'.occ b) : M = M' := by
  ext x
  · rw [← occ_natCast, ← occ_natCast, h]
  · rw [← not_iff_not, ← occ_holeSite, ← occ_holeSite, h]

/-- The charge: number of particles minus number of holes. -/
def charge (M : Maya) : ℤ := (M.P.card : ℤ) - M.H.card

/-- The energy: a particle at `b ≥ 0` costs `b`, a hole at `b < 0` costs `−b`. -/
def energy (M : Maya) : ℕ := ∑ p ∈ M.P, p + ∑ h ∈ M.H, (h + 1)

section Weight

variable {G : Type*} [CommGroup G]

/-- **The one-body weight** of the potential `φ`: `∏_{occupied} φ / ∏_{sea} φ`, i.e.
`∏_{p ∈ P} φ(p) / ∏_{h ∈ H} φ(−h − 1)`. -/
def weight (φ : ℤ → G) (M : Maya) : G := (∏ p ∈ M.P, φ p) / ∏ h ∈ M.H, φ (holeSite h)

/-- One-body weights are multiplicative in the potential. -/
theorem weight_mul (φ ψ : ℤ → G) (M : Maya) :
    weight (φ * ψ) M = weight φ M * weight ψ M := by
  simp only [weight, Pi.mul_apply, prod_mul_distrib]; rw [div_mul_div_comm]

/-- The weight of the vacuum `{b < A}`: `∏_{0 ≤ b < A} φ(b)` if `A ≥ 0`, and
`(∏_{A ≤ b < 0} φ(b))⁻¹` if `A < 0`. -/
noncomputable def seaWeight (φ : ℤ → G) (A : ℤ) : G :=
  if 0 ≤ A then ∏ b ∈ Ico 0 A, φ b else (∏ b ∈ Ico A 0, φ b)⁻¹

theorem seaWeight_zero (φ : ℤ → G) : seaWeight φ 0 = 1 := by simp [seaWeight]

theorem seaWeight_of_nonpos (φ : ℤ → G) {A : ℤ} (hA : A ≤ 0) :
    seaWeight φ A = (∏ b ∈ Ico A 0, φ b)⁻¹ := by
  rcases hA.lt_or_eq with h | rfl
  · simp [seaWeight, not_le.mpr h]
  · simp [seaWeight]

/-- Filling the site `A` multiplies the vacuum weight by `φ(A)`. -/
theorem seaWeight_succ (φ : ℤ → G) (A : ℤ) : seaWeight φ (A + 1) = seaWeight φ A * φ A := by
  rcases le_or_gt 0 A with h | h
  · rw [seaWeight, ite_eq_left (by omega), seaWeight, ite_eq_left h]
    have e : Ico 0 (A + 1) = insert A (Ico 0 A) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    rw [e, prod_insert (by simp), mul_comm]
  · rw [seaWeight_of_nonpos φ (by omega), seaWeight_of_nonpos φ h.le]
    have e1 : Ico A 0 = insert A (Ico (A + 1) 0) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    rw [e1, prod_insert (by simp)]
    group

/-- If the vacuum weight is the sum of a one-site increment, `seaWeight` is determined by
`seaWeight_succ` and `seaWeight_zero`. -/
theorem seaWeight_eq_of_succ (φ : ℤ → G) (s : ℤ → G) (h0 : s 0 = 1)
    (hs : ∀ A, s (A + 1) = s A * φ A) (A : ℤ) : seaWeight φ A = s A := by
  induction A using Int.induction_on with
  | zero => rw [seaWeight_zero, h0]
  | succ k ih => rw [seaWeight_succ, hs, ih]
  | pred k ih =>
    have h1 := seaWeight_succ φ (-(k : ℤ) - 1)
    have h2 := hs (-(k : ℤ) - 1)
    rw [show -(k : ℤ) - 1 + 1 = -k by ring, ih] at h1
    rw [show -(k : ℤ) - 1 + 1 = -k by ring] at h2
    exact mul_right_cancel (h1.symm.trans h2)

/-! ## Windows -/

/-- `[A, B)` is a **window** for `M`: every site below `A` is occupied and every site from `B` on
is empty. -/
def IsWindow (M : Maya) (A B : ℤ) : Prop := (∀ b < A, M.occ b) ∧ ∀ b, B ≤ b → ¬ M.occ b

/-- A lower edge: below it every site is occupied. -/
def bot (M : Maya) : ℤ := -((∑ h ∈ M.H, (h + 1) : ℕ) : ℤ)

/-- An upper edge: from it on every site is empty. -/
def top (M : Maya) : ℤ := ((∑ p ∈ M.P, (p + 1) : ℕ) : ℤ)

theorem bot_nonpos (M : Maya) : M.bot ≤ 0 := by unfold bot; omega

theorem top_nonneg (M : Maya) : 0 ≤ M.top := by unfold top; omega

theorem le_holeSite (M : Maya) {h : ℕ} (hh : h ∈ M.H) : M.bot ≤ holeSite h := by
  have := single_le_sum (f := fun h => h + 1) (fun _ _ => Nat.zero_le _) hh
  unfold bot holeSite; omega

theorem lt_top (M : Maya) {p : ℕ} (hp : p ∈ M.P) : (p : ℤ) < M.top := by
  have := single_le_sum (f := fun p => p + 1) (fun _ _ => Nat.zero_le _) hp
  unfold top; omega

theorem occ_of_lt_bot (M : Maya) {b : ℤ} (hb : b < M.bot) : M.occ b := by
  have hb0 : b < 0 := lt_of_lt_of_le hb M.bot_nonpos
  rw [occ_of_neg M hb0]
  intro hmem
  have := M.le_holeSite hmem
  unfold holeSite at this; omega

theorem not_occ_of_top_le (M : Maya) {b : ℤ} (hb : M.top ≤ b) : ¬ M.occ b := by
  rw [occ_of_nonneg M (le_trans M.top_nonneg hb)]
  intro hmem
  have := M.lt_top hmem
  omega

/-- The base case of the window formula: the window `[A, B)` contains all defects. -/
theorem weight_window_base (φ : ℤ → G) (M : Maya) {A B : ℤ} (hA : A ≤ M.bot) (hB : M.top ≤ B) :
    weight φ M = (∏ b ∈ (Ico A B).filter M.occ, φ b) * seaWeight φ A := by
  have hA0 : A ≤ 0 := hA.trans M.bot_nonpos
  rw [← prod_filter_mul_prod_filter_not ((Ico A B).filter M.occ) (fun b => 0 ≤ b)]
  have e1 : ((Ico A B).filter M.occ).filter (fun b => 0 ≤ b) = M.P.image (fun p : ℕ => (p : ℤ)) := by
    ext b
    simp only [mem_filter, mem_Ico, mem_image]
    constructor
    · rintro ⟨⟨-, ho⟩, hb⟩
      rw [occ_of_nonneg M hb] at ho
      exact ⟨b.toNat, ho, by omega⟩
    · rintro ⟨p, hp, rfl⟩
      have := M.lt_top hp
      exact ⟨⟨⟨by omega, by omega⟩, (occ_natCast M p).mpr hp⟩, by positivity⟩
  have e2 : ((Ico A B).filter M.occ).filter (fun b => ¬ 0 ≤ b) =
      Ico A 0 \ M.H.image holeSite := by
    ext b
    simp only [mem_filter, mem_Ico, mem_sdiff, mem_image, not_le]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, ho⟩, hb⟩
      rw [occ_of_neg M hb] at ho
      refine ⟨⟨h1, hb⟩, ?_⟩
      rintro ⟨h, hh, rfl⟩
      have : (-holeSite h - 1).toNat = h := by unfold holeSite; omega
      rw [this] at ho; exact ho hh
    · rintro ⟨⟨h1, hb⟩, hn⟩
      refine ⟨⟨⟨h1, by have := M.top_nonneg; omega⟩, ?_⟩, hb⟩
      rw [occ_of_neg M hb]
      intro hmem
      exact hn ⟨_, hmem, by unfold holeSite; omega⟩
  have hsub : M.H.image holeSite ⊆ Ico A 0 := by
    intro b hb
    obtain ⟨h, hh, rfl⟩ := mem_image.mp hb
    have := M.le_holeSite hh
    simp only [mem_Ico]; unfold holeSite at this ⊢; omega
  rw [e1, e2, prod_image (fun x _ y _ h => by exact_mod_cast h), seaWeight_of_nonpos φ hA0,
    ← prod_sdiff hsub, prod_image (fun x _ y _ h => holeSite_injective h), weight]
  simp [div_eq_mul_inv, mul_comm, mul_assoc]
  rw [mul_left_comm, mul_inv_cancel_left]

/-- One step of the window formula: moving the lower edge of the window across an occupied
site does not change the right-hand side. -/
theorem window_step (φ : ℤ → G) (M : Maya) {c B : ℤ} (hc : M.occ c) (hcB : c < B) :
    (∏ b ∈ (Ico c B).filter M.occ, φ b) * seaWeight φ c =
      (∏ b ∈ (Ico (c + 1) B).filter M.occ, φ b) * seaWeight φ (c + 1) := by
  have e : (Ico c B).filter M.occ = insert c ((Ico (c + 1) B).filter M.occ) := by
    ext b
    simp only [mem_filter, mem_Ico, mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, ho⟩
      rcases eq_or_lt_of_le h1 with rfl | h
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨by omega, h2⟩, ho⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, ho⟩)
      · exact ⟨⟨le_rfl, hcB⟩, hc⟩
      · exact ⟨⟨by omega, h2⟩, ho⟩
  rw [e, prod_insert (by simp), seaWeight_succ]
  ac_rfl

/-- **The window formula.** If `[A, B)` is a window for `M`, then
`weight φ M = ∏_{b ∈ [A, B) occupied} φ(b) · seaWeight φ A`. -/
theorem weight_window (φ : ℤ → G) {M : Maya} {A B : ℤ} (hW : M.IsWindow A B) :
    weight φ M = (∏ b ∈ (Ico A B).filter M.occ, φ b) * seaWeight φ A := by
  set A₁ := min A M.bot
  set B₁ := max B M.top
  have hF : ∀ C, (Ico C B).filter M.occ = (Ico C B₁).filter M.occ := fun C => by
    ext b
    simp only [mem_filter, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, ho⟩; exact ⟨⟨h1, by omega⟩, ho⟩
    · rintro ⟨⟨h1, -⟩, ho⟩
      exact ⟨⟨h1, by by_contra h; exact hW.2 b (by omega) ho⟩, ho⟩
  rw [hF, weight_window_base φ M (min_le_right _ _) (le_max_right _ _)]
  have step : ∀ t : ℕ, A₁ + t ≤ A →
      (∏ b ∈ (Ico A₁ B₁).filter M.occ, φ b) * seaWeight φ A₁ =
        (∏ b ∈ (Ico (A₁ + t) B₁).filter M.occ, φ b) * seaWeight φ (A₁ + t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      have hc : M.occ (A₁ + t) := hW.1 _ (by omega)
      have hcB : A₁ + t < B₁ := by
        by_contra h; exact hW.2 _ (by omega) hc
      rw [ih (by omega), window_step φ M hc hcB]
      push_cast; ring_nf
  have := step (A - A₁).toNat (by omega)
  rwa [show A₁ + ((A - A₁).toNat : ℤ) = A by omega] at this

/-! ## Charge and energy as one-body weights -/

/-- The charge is the one-body weight of the constant potential `1` (in `Multiplicative ℤ`). -/
theorem weight_const (M : Maya) :
    weight (fun _ => Multiplicative.ofAdd (1 : ℤ)) M = Multiplicative.ofAdd M.charge := by
  simp only [weight, prod_const, charge]
  apply Multiplicative.toAdd.injective
  simp

/-- The energy is the one-body weight of the potential `b` (in `Multiplicative ℤ`). -/
theorem weight_ofAdd (M : Maya) :
    weight (fun b => Multiplicative.ofAdd b) M = Multiplicative.ofAdd (M.energy : ℤ) := by
  apply Multiplicative.toAdd.injective
  simp only [weight, toAdd_div, toAdd_prod, toAdd_ofAdd, energy, holeSite]
  push_cast
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  exact sum_congr rfl fun _ _ => by ring

/-- The charge of the vacuum `{b < A}` is `A`. -/
theorem seaWeight_const (A : ℤ) :
    seaWeight (fun _ => Multiplicative.ofAdd (1 : ℤ)) A = Multiplicative.ofAdd A :=
  seaWeight_eq_of_succ _ _ (by simp) (fun A => by rw [← ofAdd_add]) A

/-- The energy of the vacuum `{b < A}` is `A(A − 1)/2`. -/
theorem two_mul_seaWeight_ofAdd (A : ℤ) :
    2 * Multiplicative.toAdd (seaWeight (fun b => Multiplicative.ofAdd b) A) = A * (A - 1) := by
  have h := seaWeight_succ (fun b => Multiplicative.ofAdd b)
  induction A using Int.induction_on with
  | zero => simp [seaWeight_zero]
  | succ k ih =>
    rw [h, toAdd_mul, toAdd_ofAdd, mul_add, ih]; ring
  | pred k ih =>
    have h1 := h (-(k : ℤ) - 1)
    rw [show -(k : ℤ) - 1 + 1 = -k by ring] at h1
    rw [h1, toAdd_mul, toAdd_ofAdd] at ih
    linarith

/-- **Charge in a window**: `charge M = #{occupied sites in [A, B)} + A`. -/
theorem charge_window {M : Maya} {A B : ℤ} (hW : M.IsWindow A B) :
    M.charge = ((Ico A B).filter M.occ).card + A := by
  have h := weight_window (fun _ => Multiplicative.ofAdd (1 : ℤ)) hW
  rw [weight_const, seaWeight_const, prod_const] at h
  have := congrArg Multiplicative.toAdd h
  simpa using this

/-- **Energy in a window**: `2·energy M = 2 ∑_{b ∈ [A, B) occupied} b + A(A − 1)`. -/
theorem two_mul_energy_window {M : Maya} {A B : ℤ} (hW : M.IsWindow A B) :
    2 * (M.energy : ℤ) = 2 * ∑ b ∈ (Ico A B).filter M.occ, b + A * (A - 1) := by
  have h := weight_window (fun b => Multiplicative.ofAdd b) hW
  rw [weight_ofAdd] at h
  have := congrArg Multiplicative.toAdd h
  rw [toAdd_ofAdd, toAdd_mul, toAdd_prod] at this
  simp only [toAdd_ofAdd] at this
  rw [this, mul_add, two_mul_seaWeight_ofAdd]

end Weight

end Maya

end RMT.Fermion
