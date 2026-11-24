import RMTlib.Tableaux.MultisetHook.Corollary4
import RMTlib.Tableaux.Hooks

/-!
# Dehaye–Han, Theorem 17: the multiset hook-content formula

`ψ_t` sends a `t`-core `λ` to the partition `μ` whose shifted parts are the coding normalised to
end at `0`: `μ_i + (t − 1 − i) = a_i − a_{t−1}` (rows from `0`; `psi`). Theorem 17:

* `ψ_t` is a bijection onto the partitions `μ` with at most `t − 1` parts whose `μ_i − i` are
  pairwise incongruent mod `t` (`psi_mem`, `psi_bijective`). The paper writes
  `{μ_i − i mod t : i = 1, …, t} = {0, …, t − 1}` with rows from `1`; the shift by one does not
  change incongruence.
* Eq. (40): `|λ| = −|μ|(|μ| + t + t²)/(2t²) + ∑_i (μ_i² + 2(t − i)μ_i)/(2t)` (`eq40`, rows from `0`).
* Eq. (41): `∏_{□∈λ} τ(h − t)τ(h + t)/τ(h)² = ∏_{i<t} (τ(−i)/τ(i))^{β_i} ∏_{□∈μ} τ(t + c)/τ(h)`
  (`eq41`), from its divisor form `eq41_div`.

The proof of Eq. (41) is the paper's: Theorem 1 plus Frobenius' row identity (the hooks of row
`i` and the gaps `ℓ_i − ℓ_j`, `j > i`, list `{1, …, ℓ_i}` once: `RMT.row_partition`), and the
same count for contents (`content_row`). Together these give
`∑_{□∈μ} [t + c] − ∑_{□∈μ} [h] = ∑_{i<j} [ℓ_i − ℓ_j] − ∑_k (t − k)[k]` (`frobenius_div`), a
statement about every partition with at most `t` rows.
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

open Classical

/-! ### Hooks and contents of a partition with at most `t` rows -/

/-- `∑_{□ ∈ ν} [h(□)]`, for `ν : Fin t → ℕ` (RMTlib's `RMT.hook` convention). -/
def hookDiv {t : ℕ} (ν : Fin t → ℕ) : ℤ →₀ ℤ :=
  ∑ i, ∑ c ∈ range (ν i), pt (RMT.hook ν i c : ℤ)

/-- `∑_{□ ∈ ν} [t + c(□)]`, the content of the cell `(i, c)` being `c − i`. -/
def contentDiv {t : ℕ} (ν : Fin t → ℕ) : ℤ →₀ ℤ :=
  ∑ i : Fin t, ∑ c ∈ range (ν i), pt ((t : ℤ) + c - i)

/-- **Frobenius' row identity, as divisors.** -/
theorem row_div {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) (i : Fin N) :
    ∑ c ∈ range (ν i), pt (RMT.hook ν i c : ℤ) +
      ∑ j ∈ Ioi i, pt ((RMT.ell ν i - RMT.ell ν j : ℕ) : ℤ) =
        ∑ k ∈ Ico 1 (RMT.ell ν i + 1), pt (k : ℤ) := by
  obtain ⟨hd, hu⟩ := RMT.row_partition ν hν i
  have hcard := card_union_of_disjoint hd
  rw [hu, Nat.card_Ico] at hcard
  have hA := card_image_le (s := range (ν i)) (f := RMT.hook ν i)
  have hB := card_image_le (s := Ioi i) (f := fun j => RMT.ell ν i - RMT.ell ν j)
  rw [card_range] at hA; rw [Fin.card_Ioi] at hB
  have hell : RMT.ell ν i = ν i + (N - 1 - i) := rfl
  have hAi : Set.InjOn (RMT.hook ν i) (range (ν i)) := card_image_iff.mp (by
    rw [card_range]; omega)
  have hBi : Set.InjOn (fun j => RMT.ell ν i - RMT.ell ν j) (Ioi i) := card_image_iff.mp (by
    rw [Fin.card_Ioi]; omega)
  rw [← hu, sum_union hd, sum_image (fun x hx y hy h => hAi hx hy h),
    sum_image (fun x hx y hy h => hBi hx hy h)]

/-- The contents of row `i`, shifted by `t`, run from `t − i` to `ℓ_i`. -/
theorem content_row {t : ℕ} (ν : Fin t → ℕ) (i : Fin t) :
    ∑ c ∈ range (ν i), pt ((t : ℤ) + c - i) =
      ∑ k ∈ Ico 1 (RMT.ell ν i + 1), pt (k : ℤ) - ∑ k ∈ Ico 1 (t - i), pt (k : ℤ) := by
  have hi := i.isLt
  have hell : RMT.ell ν i + 1 = ν i + (t - i) := by unfold RMT.ell; omega
  rw [← sum_Ico_consecutive _ (show 1 ≤ t - i by omega) (show t - i ≤ RMT.ell ν i + 1 by omega),
    add_sub_cancel_left, sum_Ico_eq_sum_range, show RMT.ell ν i + 1 - (t - i) = ν i by omega]
  refine sum_congr rfl fun c _ => ?_
  congr 1; push_cast [Nat.cast_sub hi.le]; ring

theorem sum_staircase_aux (t : ℕ) :
    ∑ n ∈ range t, ∑ k ∈ Ico 1 (n + 1), pt (k : ℤ) = ∑ k ∈ Ico 1 t, ((t : ℤ) - k) • pt (k : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, ih]
    have top : ∑ k ∈ Ico 1 (t + 1), ((t : ℤ) - k) • pt (k : ℤ) =
        ∑ k ∈ Ico 1 t, ((t : ℤ) - k) • pt (k : ℤ) := by
      rcases Nat.eq_zero_or_pos t with rfl | htp
      · simp
      · rw [sum_Ico_succ_top (by omega), sub_self, zero_smul, add_zero]
    rw [← top, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    push_cast; rw [show (t : ℤ) + 1 - k = (t - k) + 1 by ring, add_smul, one_smul]

/-- `∑_{i<t} ∑_{k=1}^{t−1−i} [k] = ∑_{k<t} (t − k)[k]`. -/
theorem sum_staircase (t : ℕ) :
    ∑ i : Fin t, ∑ k ∈ Ico 1 (t - i), pt (k : ℤ) = ∑ k ∈ Ico 1 t, ((t : ℤ) - k) • pt (k : ℤ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ k ∈ Ico 1 (t - i), pt (k : ℤ)), ← sum_staircase_aux,
    ← sum_range_reflect]
  exact sum_congr rfl fun n hn => by
    rw [mem_range] at hn; rw [show t - (t - 1 - n) = n + 1 by omega]

/-- **Hook-content as divisors**: `∑_{□∈ν} [t + c] − ∑_{□∈ν} [h] = ∑_{i<j} [ℓ_i − ℓ_j] − ∑_k (t − k)[k]`,
for every partition `ν` with at most `t` rows. -/
theorem frobenius_div {t : ℕ} (ν : Fin t → ℕ) (hν : Antitone ν) :
    contentDiv ν - hookDiv ν =
      ∑ i, ∑ j ∈ Ioi i, pt ((RMT.ell ν i - RMT.ell ν j : ℕ) : ℤ) -
        ∑ k ∈ Ico 1 t, ((t : ℤ) - k) • pt (k : ℤ) := by
  have hh : hookDiv ν = ∑ i, (∑ k ∈ Ico 1 (RMT.ell ν i + 1), pt (k : ℤ) -
      ∑ j ∈ Ioi i, pt ((RMT.ell ν i - RMT.ell ν j : ℕ) : ℤ)) :=
    sum_congr rfl fun i _ => by rw [← row_div ν hν i]; abel
  rw [contentDiv, hh, sum_congr rfl fun i _ => content_row ν i, ← sum_staircase]
  simp only [sum_sub_distrib]
  abel

/-! ### The map `ψ_t` -/

/-- **`ψ_t(λ)`**: `μ_i = a_i − a_{t−1} − (t − 1 − i)`. -/
def psi (t : ℕ) (μ : YoungDiagram) : Fin t → ℕ := fun i =>
  (aCoding t μ i - aCoding t μ ⟨t - 1, by have := i.isLt; omega⟩ - ((t - 1 - i : ℕ) : ℤ)).toNat

/-- The target of `ψ_t`: partitions with at most `t − 1` rows whose `μ_i − i` are incongruent
mod `t`. -/
def IsPsiTarget (t : ℕ) (ν : Fin t → ℕ) : Prop :=
  Antitone ν ∧ (∀ i : Fin t, (i : ℕ) + 1 = t → ν i = 0) ∧
    ∀ i j : Fin t, ((ν i : ℤ) - i) % t = ((ν j : ℤ) - j) % t → i = j

section Psi

variable {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hμ : IsTCore t μ)
include ht hμ

theorem aCoding_gap {i j : Fin t} (h : i ≤ j) :
    aCoding t μ j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ aCoding t μ i :=
  StrictAnti.add_le (aCoding_strictAnti (complete ht (stable_of_core ht hμ)).card) h

theorem psi_cast (i : Fin t) :
    (psi t μ i : ℤ) = aCoding t μ i - aCoding t μ ⟨t - 1, by omega⟩ - ((t - 1 - i : ℕ) : ℤ) := by
  unfold psi
  have hgap := aCoding_gap ht hμ (i := i) (j := ⟨t - 1, by omega⟩)
    (Fin.le_iff_val_le_val.mpr (by have := i.isLt; simp; omega))
  have hi := i.isLt
  have e : ((t - 1 - i : ℕ) : ℤ) = ((t - 1 : ℕ) : ℤ) - (i : ℕ) := by
    rw [Nat.cast_sub (by omega)]
  simp only at hgap
  rw [Int.toNat_of_nonneg (by rw [e]; linarith)]

theorem ell_psi (i : Fin t) :
    (RMT.ell (psi t μ) i : ℤ) = aCoding t μ i - aCoding t μ ⟨t - 1, by omega⟩ := by
  unfold RMT.ell; push_cast; rw [psi_cast ht hμ]; ring

/-- **`ψ_t(λ)` lies in the target.** -/
theorem psi_mem : IsPsiTarget t (psi t μ) := by
  have hV := complete ht (stable_of_core ht hμ)
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h1 := psi_cast ht hμ i; have h2 := psi_cast ht hμ j
    have := aCoding_gap ht hμ hij
    have hi := i.isLt; have hj := j.isLt; have := Fin.le_iff_val_le_val.mp hij
    push_cast [Nat.cast_sub (show (i : ℕ) ≤ t - 1 by omega),
      Nat.cast_sub (show (j : ℕ) ≤ t - 1 by omega), Nat.cast_sub (show 1 ≤ t by omega)] at h1 h2 this
    omega
  · intro i hi
    have e : i = ⟨t - 1, by omega⟩ := Fin.ext (by simp; omega)
    have := psi_cast ht hμ ⟨t - 1, by omega⟩
    rw [e]; simp at this; omega
  · intro i j h
    have h1 := psi_cast ht hμ i; have h2 := psi_cast ht hμ j
    have hi := i.isLt; have hj := j.isLt
    apply (aCoding_strictAnti hV.card).injective
    apply hV.inj _ (aCoding_mem hV.card i) _ (aCoding_mem hV.card j)
    rw [emod_eq_iff] at h ⊢
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    push_cast [Nat.cast_sub (show (i : ℕ) ≤ t - 1 by omega),
      Nat.cast_sub (show (j : ℕ) ≤ t - 1 by omega), Nat.cast_sub (show 1 ≤ t by omega)] at h1 h2
    linarith

end Psi

theorem sum_aCoding_charge {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hμ : IsTCore t μ) :
    2 * ∑ i, aCoding t μ i = -((t : ℤ) * (t + 1)) := by
  have hs := stable_of_core ht hμ
  rw [sum_aCoding (complete ht hs).card (fun a => a)]
  exact charge ht hs

/-- **`ψ_t` is a bijection onto its target.** -/
theorem psi_bijective {t : ℕ} (ht : 0 < t) (ν : Fin t → ℕ) (hν : IsPsiTarget t ν) :
    ∃! μ, IsTCore t μ ∧ psi t μ = ν := by
  obtain ⟨hanti, hlast, hres⟩ := hν
  let ℓ : Fin t → ℤ := fun i => ν i + ((t - 1 - i : ℕ) : ℤ)
  have hℓ : StrictAnti ℓ := by
    intro i j hij
    have := hanti hij.le; have := Fin.lt_def.mp hij; have := j.isLt
    simp only [ℓ]; push_cast [Nat.cast_sub (show (i : ℕ) ≤ t - 1 by omega),
      Nat.cast_sub (show (j : ℕ) ≤ t - 1 by omega)]; omega
  have hℓres : ∀ i j, ℓ i % t = ℓ j % t → i = j := by
    intro i j h
    apply hres i j
    rw [emod_eq_iff] at h ⊢
    have hi := i.isLt; have hj := j.isLt
    simp only [ℓ] at h
    push_cast [Nat.cast_sub (show (i : ℕ) ≤ t - 1 by omega),
      Nat.cast_sub (show (j : ℕ) ≤ t - 1 by omega)] at h
    convert h using 1; ring
  have hW : Complete t (univ.image ℓ) := by
    refine ⟨?_, by rw [card_image_of_injective _ hℓ.injective, card_univ, Fintype.card_fin]⟩
    intro x hx y hy h
    obtain ⟨i, -, rfl⟩ := mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := mem_image.mp hy
    rw [hℓres i j h]
  -- normalise: `a = ℓ − m` with `∑ a = −t(t + 1)/2`
  set X := ∑ x ∈ univ.image ℓ, x / (t : ℤ)
  let a : Fin t → ℤ := fun i => ℓ i - (t + X)
  have hsumℓ : 2 * ∑ i, ℓ i = t * (t - 1 : ℤ) + 2 * t * X := by
    rw [← sum_image (f := fun x => x) (fun i _ j _ h => hℓ.injective h)]
    have hsplit : ∑ x ∈ univ.image ℓ, x = ∑ x ∈ univ.image ℓ, x % (t : ℤ) + t * X := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun x _ => (Int.emod_add_mul_ediv x t).symm
    rw [hsplit, hW.sum_emod' ht (fun x => x)]
    have := Finset.sum_range_id_mul_two t
    have := congrArg (fun z : ℕ => (z : ℤ)) this
    push_cast [Nat.cast_sub ht] at this
    linarith
  have hsuma : 2 * ∑ i, a i = -((t : ℤ) * (t + 1)) := by
    simp only [a, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  let v : Fin t → ℚ := fun i => a i + ((t : ℚ) + 1) / 2
  have hv : IsVCoding t v := by
    refine ⟨fun i j hij => ?_, ?_, a, fun i => rfl, fun i j h => hℓres i j ?_⟩
    · simp only [v, a]; have := hℓ hij; push_cast; linarith [(show (ℓ j : ℚ) < ℓ i by exact_mod_cast this)]
    · simp only [v, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      have := congrArg (fun z : ℤ => (z : ℚ)) hsuma; push_cast at this; linarith
    · unfold Int.ModEq at h; rw [emod_eq_iff] at h ⊢; simpa [a] using h
  obtain ⟨μ, hμ, hvμ⟩ := exists_of_isVCoding ht hv
  have ha : aCoding t μ = a := funext fun i => by
    have := congrFun hvμ i; simp only [vCoding, v, add_left_inj, Int.cast_inj] at this; exact this
  have hψμ : psi t μ = ν := funext fun i => by
    have := psi_cast ht hμ i
    rw [ha] at this
    have hL : ν ⟨t - 1, by omega⟩ = 0 := hlast _ (by simp; omega)
    simp only [a, ℓ, hL] at this
    have hi := i.isLt
    push_cast at this
    omega
  refine ⟨μ, ⟨hμ, hψμ⟩, ?_⟩
  · rintro μ' ⟨hμ', hψ⟩
    apply eq_of_vCoding_eq ht hμ' hμ
    have hc : ∀ i, aCoding t μ' i - aCoding t μ i =
        aCoding t μ' ⟨t - 1, by omega⟩ - aCoding t μ ⟨t - 1, by omega⟩ := by
      intro i
      have h1 := psi_cast ht hμ' i; have h2 := psi_cast ht hμ i
      have h3 : psi t μ' i = psi t μ i := by
        rw [hψ, hψμ]
      rw [h3] at h1; linarith
    have hs1 := sum_aCoding_charge ht hμ'
    have hs2 := sum_aCoding_charge ht hμ
    have hc0 : aCoding t μ' ⟨t - 1, by omega⟩ - aCoding t μ ⟨t - 1, by omega⟩ = 0 := by
      have : ∑ i, (aCoding t μ' i - aCoding t μ i) =
          t * (aCoding t μ' ⟨t - 1, by omega⟩ - aCoding t μ ⟨t - 1, by omega⟩) := by
        rw [sum_congr rfl fun i _ => hc i, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [sum_sub_distrib] at this
      have : (t : ℤ) * (aCoding t μ' ⟨t - 1, by omega⟩ - aCoding t μ ⟨t - 1, by omega⟩) = 0 := by
        linarith
      exact (mul_eq_zero.mp this).resolve_left (by omega)
    funext i
    have := hc i
    simp only [vCoding]
    rw [show aCoding t μ' i = aCoding t μ i by linarith]

/-! ### Eq. (41) -/

/-- **Eq. (41) as divisors**: `{h − t} + {h + t} + ∑ β_i [i] + ∑_{□∈μ} [h]
= 2{h} + ∑ β_i [−i] + ∑_{□∈μ} [t + c]`, with `μ = ψ_t(λ)`. -/
theorem eq41_div {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hμ : IsTCore t μ) :
    toDiv ((hooks μ).map (· - (t : ℤ))) + toDiv ((hooks μ).map (· + (t : ℤ))) +
        ∑ i ∈ Ico 1 t, beta t μ i • pt (i : ℤ) + hookDiv (psi t μ) =
      2 • toDiv (hooks μ) + ∑ i ∈ Ico 1 t, beta t μ i • pt (-(i : ℤ)) + contentDiv (psi t μ) := by
  have hV := complete ht (stable_of_core ht hμ)
  have hdiv := congrArg toDiv ((theorem1 t ht).divisor μ hμ)
  simp only [divisorLHS, divisorRHS, toDiv_add, toDiv_nsmul, toDiv_sum, toDiv_singleton] at hdiv
  have hfrob := frobenius_div (psi t μ) (psi_mem ht hμ).1
  -- the pair differences of the coding are the gaps of `ψ_t(λ)`
  have hgaps : toDiv (pairDiffs (aCoding t μ)) =
      ∑ i, ∑ j ∈ Ioi i, pt ((RMT.ell (psi t μ) i - RMT.ell (psi t μ) j : ℕ) : ℤ) := by
    rw [pairDiffs, toDiv_map]
    change ∑ p ∈ (univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2),
      pt (aCoding t μ p.1 - aCoding t μ p.2) = _
    rw [sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_filter]
    have : (univ : Finset (Fin t)).filter (fun j => i < j) = Ioi i := by ext j; simp
    rw [this]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_Ioi] at hj
    have h1 := ell_psi ht hμ i; have h2 := ell_psi ht hμ j
    have hle : RMT.ell (psi t μ) j ≤ RMT.ell (psi t μ) i := by
      have := aCoding_gap ht hμ hj.le; omega
    rw [Nat.cast_sub hle, h1, h2]; ring_nf
  rw [hgaps] at hdiv
  have hnat : ∀ i ∈ Ico 1 t, (beta t μ i + t - i) • pt (i : ℤ) =
      beta t μ i • pt (i : ℤ) + ((t : ℤ) - i) • pt (i : ℤ) := fun i hi => by
    rw [mem_Ico] at hi
    rw [show beta t μ i + t - i = beta t μ i + (t - i) by omega, add_smul,
      ← Nat.cast_smul_eq_nsmul ℤ (t - i), Nat.cast_sub hi.2.le]
  rw [sum_congr rfl hnat, sum_add_distrib] at hdiv
  rw [← sub_eq_zero]
  have : contentDiv (psi t μ) = hookDiv (psi t μ) +
      (∑ i, ∑ j ∈ Ioi i, pt ((RMT.ell (psi t μ) i - RMT.ell (psi t μ) j : ℕ) : ℤ) -
        ∑ k ∈ Ico 1 t, ((t : ℤ) - k) • pt (k : ℤ)) := by rw [← hfrob]; abel
  rw [this, ← sub_eq_zero.mpr hdiv]
  abel

/-- Rearranging in a commutative group. -/
theorem rearrange41 {G : Type*} [CommGroup G] {A B H P N Hm Cm : G}
    (h : A * B * P * Hm = H ^ 2 * N * Cm) : A * B / H ^ 2 = N / P * (Cm / Hm) := by
  have h' := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at h' ⊢
  rw [← sub_eq_zero]
  calc _ = (Additive.ofMul A + Additive.ofMul B + Additive.ofMul P + Additive.ofMul Hm) -
        (2 • Additive.ofMul H + Additive.ofMul N + Additive.ofMul Cm) := by abel
    _ = 0 := by rw [h', sub_self]

/-- **Dehaye–Han, Eq. (41)**: for any weight `τ` with values in a commutative group,
`∏_{□∈λ} τ(h − t)τ(h + t)/τ(h)² = ∏_{i<t} (τ(−i)/τ(i))^{β_i} ∏_{□∈μ} τ(t + c)/τ(h)`,
`μ = ψ_t(λ)`. -/
theorem eq41 {G : Type*} [CommGroup G] (τ : ℤ → G) {t : ℕ} (ht : 0 < t) {μ : YoungDiagram}
    (hμ : IsTCore t μ) :
    ((hooks μ).map fun h => τ (h - t) * τ (h + t) / τ h ^ 2).prod =
      (∏ i ∈ Ico 1 t, (τ (-(i : ℤ)) / τ i) ^ beta t μ i) *
        ∏ i, ∏ c ∈ range (psi t μ i),
          τ ((t : ℤ) + c - i) / τ (RMT.hook (psi t μ) i c : ℤ) := by
  have e := congrArg (fun D => (evalU τ D).toMul) (eq41_div ht hμ)
  have hc : ∀ f : ℤ → ℤ, toDiv ((hooks μ).map f) = ∑ c ∈ μ.cells, pt (f (hook μ c)) :=
    fun f => by rw [hooks, Multiset.map_map, toDiv_map]; rfl
  have hc' : toDiv (hooks μ) = ∑ c ∈ μ.cells, pt (hook μ c) := by
    rw [hooks, toDiv_map]; rfl
  simp only [hc, hc', hookDiv, contentDiv, map_add, map_sum, map_nsmul, toMul_add, toMul_sum,
    toMul_nsmul, evalU_pt] at e
  have hm : ((hooks μ).map fun h => τ (h - t) * τ (h + t) / τ h ^ 2).prod =
      ∏ c ∈ μ.cells, τ (hook μ c - t) * τ (hook μ c + t) / τ (hook μ c) ^ 2 := by
    rw [hooks, Multiset.map_map]; rfl
  rw [hm, prod_div_distrib, prod_mul_distrib, prod_pow]
  simp only [div_pow, prod_div_distrib]
  exact rearrange41 e

/-! ### Eq. (40) -/

theorem sum_fin_cast (t : ℕ) : 2 * ∑ i : Fin t, (i : ℚ) = t * (t - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℚ))]
  have := Finset.sum_range_id_mul_two t
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · simp
  have := congrArg (fun z : ℕ => (z : ℚ)) this; push_cast [Nat.cast_sub htp] at this
  linarith

theorem sum_fin_sq_cast (t : ℕ) : 6 * ∑ i : Fin t, (i : ℚ) ^ 2 = (t - 1) * t * (2 * t - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℚ) ^ 2)]
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

/-- The algebra behind Eq. (40). -/
theorem eq40_algebra (t : ℕ) (ht : 0 < t) (ψ : Fin t → ℚ) :
    (∑ i, (ψ i - i + ((t : ℚ) - 1) / 2 - (∑ j, ψ j) / t) ^ 2) / (2 * t) - ((t : ℚ) ^ 2 - 1) / 24 =
      -(∑ j, ψ j) * ((∑ j, ψ j) + t + t ^ 2) / (2 * t ^ 2) +
        ∑ i, (ψ i ^ 2 + 2 * (t - i) * ψ i) / (2 * t) := by
  set M := ∑ j, ψ j
  set c : ℚ := ((t : ℚ) - 1) / 2 - M / t
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast ht.ne'
  have e1 : ∀ i : Fin t, (ψ i - i + ((t : ℚ) - 1) / 2 - M / t) ^ 2 =
      ψ i ^ 2 - 2 * ((i : ℚ) * ψ i) + 2 * c * ψ i + (i : ℚ) ^ 2 - 2 * c * i + c ^ 2 :=
    fun i => by simp only [c]; ring
  have e2 : ∀ i : Fin t, (ψ i ^ 2 + 2 * (t - i) * ψ i) / (2 * t) =
      (ψ i ^ 2 + 2 * t * ψ i - 2 * ((i : ℚ) * ψ i)) / (2 * t) := fun i => by ring
  simp only [e1, e2, ← sum_div, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  have s1 := sum_fin_cast t
  have s2 := sum_fin_sq_cast t
  set S1 := ∑ i : Fin t, (i : ℚ)
  set S2 := ∑ i : Fin t, (i : ℚ) ^ 2
  rw [show S1 = t * (t - 1) / 2 by linarith, show S2 = (t - 1) * t * (2 * t - 1) / 6 by linarith]
  simp only [c]
  field_simp
  ring

/-- **Dehaye–Han, Eq. (40)**: `|λ| = −|μ|(|μ| + t + t²)/(2t²) + ∑_i (μ_i² + 2(t − i)μ_i)/(2t)`
for `μ = ψ_t(λ)` (rows from `0`). -/
theorem eq40 {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hμ : IsTCore t μ) :
    (μ.cells.card : ℚ) =
      -(∑ j, (psi t μ j : ℚ)) * ((∑ j, (psi t μ j : ℚ)) + t + t ^ 2) / (2 * t ^ 2) +
        ∑ i, ((psi t μ i : ℚ) ^ 2 + 2 * (t - i) * psi t μ i) / (2 * t) := by
  rw [← eq40_algebra t ht, (theorem1 t ht).size μ hμ]
  congr 2
  -- `v_i = μ_i − i + (t − 1)/2 − |μ|/t`
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast ht.ne'
  set aL := aCoding t μ ⟨t - 1, by omega⟩
  have hcast : ∀ i : Fin t, (aCoding t μ i : ℚ) = psi t μ i + (t - 1 - i) + aL := fun i => by
    have := psi_cast ht hμ i; have hi := i.isLt
    push_cast [Nat.cast_sub (show (i : ℕ) ≤ t - 1 by omega), Nat.cast_sub (show 1 ≤ t by omega)]
      at this
    have := congrArg (fun z : ℤ => (z : ℚ)) this; push_cast at this; linarith
  have hsum := congrArg (fun z : ℤ => (z : ℚ)) (sum_aCoding_charge ht hμ)
  push_cast at hsum
  simp only [hcast, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have s1 := sum_fin_cast t
  have haL : (aL : ℚ) = -t - (∑ j, (psi t μ j : ℚ)) / t := by
    field_simp; linarith
  refine sum_congr rfl fun i _ => ?_
  simp only [vCoding, hcast, haL]
  ring

end

end RMT.MultisetHook
