import Mathlib

/-!
# The Maya generating function and the sign-Molien series (RMTlib#163)

The share of the condensed edition's `pieriCone` (RH-Dual#239) is `1/[k]_q!` with `q = P^N`, and
its proof sums `sign τ / |det(1 − τ/q)|` over `τ ∈ S_k`: the sign-character Molien series of `S_k`
at `t = 1/q`. This file gives the fermionic (Maya) account of that number.

* `configs k n`: the `k`-particle Maya configurations on `0, 1, 2, …` with total position `n`.
* `card_configs_succ`: **the recursion**. Either site `0` is occupied (remove it and shift the rest
  down) or not (shift everything down).
* `F k`, `F_succ`, `F_mul_prod`: **the generating function** `F_k = Σ_n #configs(k, n) Xⁿ`
  satisfies `F_{k+1} = X^k F_k + X^{k+1} F_{k+1}`, hence `F_k · ∏_{i=1}^{k} (1 − X^i) = X^{C(k,2)}`.
  This is the sign-Molien series of `S_k` (lit: Molien; the alternating polynomials are the
  Vandermonde times the symmetric ones). Its bosonic twin `1/∏(1 − X^i)` counts partitions with at
  most `k` rows.
* `factor_eq`, `share_eq`: **the share**. At `t = 1/q`,
  `t^{C(k,2)} ∏_{i<k} (1 − t)/(1 − t^{i+1}) = 1/[k]_q!`. The left side is `(1 − t)^k F_k(t)`:
  `k` free particles with Boltzmann weights `t^n = q^{−n}`, conditioned to be strictly ordered (the
  Pauli fraction). As `q → 1` it tends to `1/k!`, the Weyl-chamber (𝔽₁) share.

The Molien sum over `S_k` itself, and `[k]_q! = Σ_w q^{inv w}`, are not proved here.
-/

open Finset PowerSeries

namespace RMT.Symmetric.MayaMolien

/-- The `k`-particle Maya configurations on `0, 1, 2, …` with total position `n`: `k`-subsets of
`{0, …, n}` with sum `n`. -/
def configs (k n : ℕ) : Finset (Finset ℕ) :=
  (range (n + 1)).powerset.filter fun s => s.card = k ∧ s.sum id = n

theorem mem_configs {k n : ℕ} {s : Finset ℕ} :
    s ∈ configs k n ↔ s.card = k ∧ s.sum id = n := by
  unfold configs
  simp only [mem_filter, mem_powerset]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, h1, h2⟩
    have h := single_le_sum (f := fun y : ℕ => y) (fun _ _ => Nat.zero_le _) hx
    have h2' : ∑ y ∈ s, y = n := h2
    rw [mem_range]
    omega

/-- Shift every particle up by one. -/
def up (t : Finset ℕ) : Finset ℕ := t.map (addRightEmbedding 1)

/-- Shift every particle down by one (for configurations avoiding `0`). -/
def down (s : Finset ℕ) : Finset ℕ := s.image (· - 1)

theorem sum_up (t : Finset ℕ) : (up t).sum id = t.sum id + t.card := by
  simp [up, sum_add_distrib]

theorem card_up (t : Finset ℕ) : (up t).card = t.card := by simp [up]

theorem zero_not_mem_up (t : Finset ℕ) : 0 ∉ up t := by simp [up]

theorem down_up (t : Finset ℕ) : down (up t) = t := by
  ext x; simp [up, down]

theorem up_down {s : Finset ℕ} (h0 : 0 ∉ s) : up (down s) = s := by
  ext x
  simp only [up, down, mem_map, mem_image, addRightEmbedding_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have : z ≠ 0 := fun h => h0 (h ▸ hz)
    rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero this)]
  · intro hx
    have : x ≠ 0 := fun h => h0 (h ▸ hx)
    exact ⟨x - 1, ⟨x, hx, rfl⟩, Nat.sub_add_cancel (Nat.pos_of_ne_zero this)⟩

theorem card_le_sum_of_pos {s : Finset ℕ} (h : ∀ x ∈ s, 0 < x) : s.card ≤ ∑ x ∈ s, x := by
  rw [card_eq_sum_ones]; exact sum_le_sum fun x hx => h x hx

/-- **The recursion on configurations**: either site `0` is occupied (remove it and shift the rest
down: `k − 1` particles, total `n − (k − 1)`), or not (shift down: `k` particles, total `n − k`). -/
theorem card_configs_succ (k n : ℕ) :
    (configs (k + 1) n).card =
      (if k ≤ n then (configs k (n - k)).card else 0) +
        (if k + 1 ≤ n then (configs (k + 1) (n - (k + 1))).card else 0) := by
  classical
  rw [← card_filter_add_card_filter_not (s := configs (k + 1) n) (p := fun s => 0 ∈ s)]
  congr 1
  · -- site `0` occupied: remove it and shift the rest down
    split_ifs with hk
    · refine card_nbij' (fun s => down (s.erase 0)) (fun t => insert 0 (up t)) ?_ ?_ ?_ ?_
      · intro s hs
        simp only [coe_filter, Set.mem_ofPred_eq, mem_coe, mem_configs] at hs ⊢
        obtain ⟨⟨hc, hsum⟩, h0⟩ := hs
        have h0' : 0 ∉ s.erase 0 := by simp
        have hu := up_down h0'
        have e1 := card_up (down (s.erase 0))
        have e2 := sum_up (down (s.erase 0))
        rw [hu] at e1 e2
        have ce : (s.erase 0).card = k := by rw [card_erase_of_mem h0, hc]; rfl
        have se : (s.erase 0).sum id = n := by
          rw [← sum_erase_add _ _ h0] at hsum; simpa using hsum
        constructor <;> omega
      · intro t ht
        simp only [mem_coe, mem_configs, coe_filter, Set.mem_ofPred_eq] at ht ⊢
        refine ⟨⟨?_, ?_⟩, mem_insert_self _ _⟩
        · rw [card_insert_of_notMem (zero_not_mem_up t), card_up, ht.1]
        · rw [sum_insert (zero_not_mem_up t), sum_up, ht.1, ht.2]; simp; omega
      · intro s hs
        simp only [coe_filter, Set.mem_ofPred_eq] at hs
        show insert 0 (up (down (s.erase 0))) = s
        rw [up_down (by simp), insert_erase hs.2]
      · intro t _
        show down ((insert 0 (up t)).erase 0) = t
        rw [erase_insert (zero_not_mem_up t), down_up]
    · apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro s hs h0
      rw [mem_configs] at hs
      have hpos : ∀ x ∈ s.erase 0, 0 < x := fun x hx => Nat.pos_of_ne_zero (ne_of_mem_erase hx)
      have h1 := card_le_sum_of_pos hpos
      rw [card_erase_of_mem h0, hs.1] at h1
      have h2 : ∑ x ∈ s, x = ∑ x ∈ s.erase 0, x := by rw [← sum_erase_add _ _ h0]; simp
      have h3 : ∑ x ∈ s, x = n := hs.2
      omega
  · -- site `0` empty: shift down
    split_ifs with hk
    · refine card_nbij' down up ?_ ?_ ?_ ?_
      · intro s hs
        simp only [coe_filter, Set.mem_ofPred_eq, mem_coe, mem_configs] at hs ⊢
        obtain ⟨⟨hc, hsum⟩, h0⟩ := hs
        have hu := up_down h0
        have e1 := card_up (down s)
        have e2 := sum_up (down s)
        rw [hu] at e1 e2
        have hsum' : s.sum id = n := hsum
        constructor <;> omega
      · intro t ht
        simp only [mem_coe, mem_configs, coe_filter, Set.mem_ofPred_eq] at ht ⊢
        refine ⟨⟨by rw [card_up, ht.1], ?_⟩, zero_not_mem_up t⟩
        rw [sum_up, ht.1, ht.2]; omega
      · intro s hs
        simp only [coe_filter, Set.mem_ofPred_eq] at hs
        exact up_down hs.2
      · intro t _
        exact down_up t
    · apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro s hs h0
      rw [mem_configs] at hs
      have hpos : ∀ x ∈ s, 0 < x := fun x hx => Nat.pos_of_ne_zero fun h => h0 (h ▸ hx)
      have h1 := card_le_sum_of_pos hpos
      have h3 : ∑ x ∈ s, x = n := hs.2
      omega


/-! ## The generating function -/

/-- **The fermionic (Maya) generating function** `F_k = Σ_n #{k-particle configurations of total n} Xⁿ`. -/
noncomputable def F (k : ℕ) : PowerSeries ℤ := PowerSeries.mk fun n => ((configs k n).card : ℤ)

theorem configs_zero (n : ℕ) : configs 0 n = if n = 0 then {∅} else ∅ := by
  ext s
  rw [mem_configs, card_eq_zero]
  split_ifs with h
  · subst h; simp only [mem_singleton]; constructor
    · exact fun h => h.1
    · rintro rfl; simp
  · simp only [notMem_empty, iff_false, not_and]
    rintro rfl; simp; omega

theorem F_zero : F 0 = 1 := by
  ext n
  simp only [F, coeff_mk, configs_zero, coeff_one]
  split_ifs <;> simp

/-- **`F_{k+1} = X^k F_k + X^{k+1} F_{k+1}`**. -/
theorem F_succ (k : ℕ) : F (k + 1) = X ^ k * F k + X ^ (k + 1) * F (k + 1) := by
  ext n
  rw [map_add, coeff_X_pow_mul', coeff_X_pow_mul']
  simp only [F, coeff_mk]
  rw [card_configs_succ]
  push_cast
  split_ifs <;> simp

/-- **The sign-Molien identity on Maya diagrams**:
`F_k · ∏_{i=1}^{k} (1 − X^i) = X^{k(k−1)/2}`, i.e. `F_k = X^{C(k,2)} / ∏ (1 − X^i)`. -/
theorem F_mul_prod (k : ℕ) :
    F k * ∏ i ∈ range k, (1 - X ^ (i + 1)) = X ^ (k * (k - 1) / 2) := by
  induction k with
  | zero => simp [F_zero]
  | succ k ih =>
    have h := F_succ k
    have h1 : F (k + 1) * (1 - X ^ (k + 1)) = X ^ k * F k := by
      rw [mul_sub, mul_one]; nth_rewrite 1 [h]; ring
    rw [prod_range_succ]
    set P := ∏ i ∈ range k, (1 - (X : PowerSeries ℤ) ^ (i + 1))
    rw [show F (k + 1) * (P * (1 - X ^ (k + 1))) = (F (k + 1) * (1 - X ^ (k + 1))) * P by ring, h1,
      mul_assoc, ih, ← pow_add]
    congr 1
    rcases k with _ | k
    · rfl
    · have : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel, this, Nat.add_mul_div_left _ _ (by norm_num)]
      ring

/-! ## The share at `t = 1/q` -/

theorem two_mul_sum_range_id (k : ℕ) : 2 * ∑ i ∈ range k, i = k * (k - 1) := by
  rw [mul_comm, Finset.sum_range_id_mul_two]

/-- One factor: `(1 − 1/q) / (1 − 1/q^{i+1}) = q^i / [i+1]_q`, with `[m]_q = 1 + q + ⋯ + q^{m−1}`. -/
theorem factor_eq {q : ℝ} (hq : 1 < q) (i : ℕ) :
    (1 - q⁻¹) / (1 - q⁻¹ ^ (i + 1)) = q ^ i / ∑ j ∈ range (i + 1), q ^ j := by
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := by linarith
  have hgeom : ∑ j ∈ range (i + 1), q ^ j = (q ^ (i + 1) - 1) / (q - 1) := geom_sum_eq (by linarith) _
  have hpow : q ^ (i + 1) - 1 ≠ 0 := by
    have : 1 < q ^ (i + 1) := one_lt_pow₀ hq (by omega)
    linarith
  rw [hgeom, inv_pow]
  field_simp
  ring

/-- **The share of `pieriCone`, on Maya diagrams**: at `t = 1/q`,
`t^{k(k−1)/2} ∏_{i<k} (1 − t)/(1 − t^{i+1}) = 1/[k]_q!`. The left side is `(1 − t)^k F_k(t)`
(`F_mul_prod`): the fermionic generating function normalised by `k` free particles, i.e. the
probability that `k` independent particles with weights `t^n` are strictly ordered. -/
theorem share_eq {q : ℝ} (hq : 1 < q) (k : ℕ) :
    q⁻¹ ^ (k * (k - 1) / 2) * ∏ i ∈ range k, (1 - q⁻¹) / (1 - q⁻¹ ^ (i + 1)) =
      (∏ i ∈ range k, ∑ j ∈ range (i + 1), q ^ j)⁻¹ := by
  have hq0 : q ≠ 0 := by positivity
  simp_rw [factor_eq hq]
  rw [prod_div_distrib, prod_pow_eq_pow_sum]
  have h2 := two_mul_sum_range_id k
  have hs : ∑ i ∈ range k, i = k * (k - 1) / 2 := by omega
  rw [hs, inv_pow, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]

end RMT.Symmetric.MayaMolien
