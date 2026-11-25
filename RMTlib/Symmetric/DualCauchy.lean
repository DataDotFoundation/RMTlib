import RMTlib.Symmetric.DualJacobiTrudi
import MeaningLib.Frame.Pattern

/-!
# The dual Cauchy identity

For values `α, β : ℕ → R` in a commutative ring and a parameter `T`,

  `Σ_{λ ⊆ m × n} T^{|λ|} s_λ(α₀, …, α_{m−1}) s_{λ'}(β₀, …, β_{n−1}) = ∏_{i<n, j<m} (1 + α_j β_i T)`

(`dual_cauchy`), the sum over the partitions `λ` with at most `m` rows and at most `n` columns.
It is the fermionic twin of the Cauchy identity `Σ_λ s_λ(α) s_λ(β) = ∏ (1 − α_j β_i)⁻¹`
(`RMT.Symmetric.cauchy`): the kernel is a polynomial, and the sum is finite.

## Proof

Induction on the number `n` of `β` variables, on the `e`-determinant side: by dual Jacobi–Trudi
(`schurV_conjV_eq_eDet`) `s_{λ'}(β) = det (e_{λ_i − i + j}(β))`. Adding the variable `β_n`
branches that determinant over the vertical strips `J` of `λ` (`eDet_succ`,
`eDet_eq_zero_of_not_isVStrip`); writing `λ = μ + 1_J`, the strips attached to a fixed `μ`
are the ones the **dual Pieri rule** adds (`esymm_mul_schurV`), so the new variable multiplies
the sum by `Σ_k (β_n T)^k e_k(α) = ∏_j (1 + α_j β_n T)` (`prod_one_add_mul_eq_sum_eV`).

This mirrors the bosonic side, where the same induction runs on horizontal strips with the
Pieri rule for `h_k`; here no RSK (bosonic or dual) is used. The dual RSK of
`RMT.RSK.GrowthSuper` / `GrowthStrips` (parity growth) is not packaged as a bijection onto
tableau pairs, so the bijective proof is not available.

## Main results

* `boxParts m B`: the partitions with at most `m` rows and parts `≤ B`.
* `schurV_zero_shape`: `s_∅ = 1`.
* `eDet_zero_index`, `eDet_eq_zero_of_lt`: the `e`-determinant with no variables, and its
  vanishing when the first part exceeds the number of variables.
* `prod_one_add_mul_eq_sum_eV`: `∏_j (1 + a_j t) = Σ_k e_k(a) t^k`.
* `map_eZ`, `map_eDet`: functoriality in the values.
* `dual_cauchy_eDet`: the dual Cauchy identity, `e`-determinant form.
* `dual_cauchy`, `dual_cauchy_one`: the dual Cauchy identity.
-/

open Finset Matrix

namespace RMT.Symmetric

variable {R : Type*} [CommRing R]

/-! ## The box of partitions -/

open Classical in
/-- **The partitions in the `m × B` box**: antitone `λ : Fin m → ℕ` with every part `≤ B`. -/
noncomputable def boxParts (m B : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun _ : Fin m => range (B + 1)).filter Antitone

theorem mem_boxParts {m B : ℕ} {l : Fin m → ℕ} : l ∈ boxParts m B ↔ Antitone l ∧ ∀ i, l i ≤ B := by
  classical
  simp only [boxParts, mem_filter, Fintype.mem_piFinset, mem_range, Nat.lt_succ_iff]
  tauto

/-! ## Small facts -/

/-- **The empty shape has one tableau**: `s_∅ = 1`. -/
theorem schurV_zero_shape (a : ℕ → R) {N : ℕ} : ∀ m : ℕ, schurV a N m 0 = 1
  | 0 => by rw [schurV_zero, if_pos rfl]
  | m + 1 => by
    have h : interl (0 : Fin N → ℕ) = {0} := by
      ext mu
      rw [mem_interl, mem_singleton]
      constructor
      · intro h; funext t; have := h.2 t; simp at this ⊢; omega
      · rintro rfl; exact ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
    rw [schurV_succ, h, sum_singleton, schurV_zero_shape a m]
    simp

/-- With no variables the `e`-determinant of a partition is `1` at `∅` and `0` otherwise. -/
theorem eDet_zero_index (a : ℕ → R) {N : ℕ} {lam : Fin N → ℕ} (hl : Antitone lam) :
    eDet a 0 (fun i => (lam i : ℤ)) = if lam = 0 then 1 else 0 := by
  rw [eDet, eZ_zero_eq_hE,
    show (of fun i j : Fin N => hE a 0 ((lam i : ℤ) - i + j)) = jtMat a 0 lam from rfl,
    det_jtMat_zero a lam hl]

/-- **More columns than variables**: if some part of the partition `λ` exceeds `n`, then
`det (e_{λ_i − i + j}(a₀, …, a_{n−1})) = 0` (its first row vanishes). -/
theorem eDet_eq_zero_of_lt (a : ℕ → R) {N n : ℕ} {lam : Fin N → ℕ} (hl : Antitone lam)
    {i : Fin N} (hi : n < lam i) : eDet a n (fun i => (lam i : ℤ)) = 0 := by
  have h0 : 0 < N := Fin.pos i
  refine det_eq_zero_of_row_eq_zero ⟨0, h0⟩ fun j => ?_
  have := hl (show (⟨0, h0⟩ : Fin N) ≤ i from Fin.mk_le_mk.mpr (Nat.zero_le _))
  simp only [of_apply]
  exact eZ_eq_zero_of_lt a (by push_cast; omega)

/-- **The generating function of the `e_k`**: `∏_{j<m} (1 + a_j t) = Σ_{k ≤ m} e_k(a) t^k`. -/
theorem prod_one_add_mul_eq_sum_eV (a : ℕ → R) (m : ℕ) (t : R) :
    ∏ j : Fin m, (1 + a j * t) = ∑ k ∈ range (m + 1), eV a m k * t ^ k := by
  classical
  rw [prod_one_add, ← sum_fiberwise_of_maps_to (g := card) (t := range (m + 1))
    (fun S _ => mem_range.mpr (Nat.lt_succ_of_le ((card_le_univ S).trans (by simp))))]
  refine sum_congr rfl fun k _ => ?_
  rw [eV, sum_mul]
  refine sum_congr (by ext S; simp [mem_powersetCard]) fun S hS => ?_
  rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp hS).2]

/-- Ring homomorphisms commute with `e_k`. -/
theorem map_eZ {S : Type*} [CommRing S] (f : R →+* S) (a : ℕ → R) (n : ℕ) (k : ℤ) :
    f (eZ a n k) = eZ (f ∘ a) n k := by
  unfold eZ
  split_ifs <;> simp [map_eV]

/-- Ring homomorphisms commute with the `e`-determinant. -/
theorem map_eDet {S : Type*} [CommRing S] (f : R →+* S) (a : ℕ → R) (m : ℕ) {N : ℕ}
    (x : Fin N → ℤ) : f (eDet a m x) = eDet (f ∘ a) m x := by
  rw [eDet, eDet, RingHom.map_det]
  congr 1
  ext i j
  simp [map_eZ]

/-! ## The dual Cauchy identity -/

/-- `ind J` is the integer indicator `indZ J`, cast. -/
theorem vsub_add_ind {N : ℕ} {lam : Fin N → ℕ} {J : Finset (Fin N)} (h : ∀ i ∈ J, 0 < lam i) :
    vsub lam J + ind J = lam := by
  funext i
  have := h i
  by_cases hi : i ∈ J <;> simp [vsub, ind, hi] at this ⊢
  omega

theorem vsub_add_ind' {N : ℕ} (mu : Fin N → ℕ) (J : Finset (Fin N)) :
    vsub (mu + ind J) J = mu := by
  funext i
  simp only [Pi.add_apply, vsub, ind]
  split_ifs <;> omega

/-- Adding `1_J` adds `|J|` boxes. -/
theorem sum_add_ind {N : ℕ} (mu : Fin N → ℕ) (J : Finset (Fin N)) :
    ∑ i, (mu + ind J) i = ∑ i, mu i + J.card := by
  classical
  simp only [Pi.add_apply, sum_add_distrib, ind, sum_boole, Nat.cast_id, filter_mem_eq_inter,
    univ_inter]

/-- **One more `β` variable multiplies the dual Cauchy sum by `∏_j (1 + α_j β_n T)`**, at fixed
`μ`: the vertical strips that dual Pieri adds to `μ`, weighted by `(β_n T)^{|J|}`. -/
theorem sum_strips_eq (α : ℕ → R) {m : ℕ} {mu : Fin m → ℕ} (hmu : Antitone mu) (t : R) :
    ∑ J ∈ (univ : Finset (Finset (Fin m))).filter (fun J => Antitone (mu + ind J)),
        t ^ J.card * schurV α m m (mu + ind J) =
      (∏ j : Fin m, (1 + α j * t)) * schurV α m m mu := by
  classical
  rw [prod_one_add_mul_eq_sum_eV, sum_mul,
    ← sum_fiberwise_of_maps_to (g := card) (t := range (m + 1))
      (fun J _ => mem_range.mpr (Nat.lt_succ_of_le ((card_le_univ J).trans (by simp))))]
  refine sum_congr rfl fun k _ => ?_
  rw [show eV α m k * t ^ k * schurV α m m mu = t ^ k * (eV α m k * schurV α m m mu) by ring,
    esymm_mul_schurV α m mu hmu k, mul_sum, filter_filter]
  refine sum_congr (by ext J; simp only [mem_filter, mem_univ, true_and]; tauto) fun J hJ => ?_
  rw [(mem_filter.mp hJ).2.1]
  rfl

/-- **The dual Cauchy identity, `e`-determinant form.** For `n ≤ B`,

  `Σ_{λ ⊆ m × B} T^{|λ|} s_λ(α₀, …, α_{m−1}) det (e_{λ_i − i + j}(β₀, …, β_{n−1}))
    = ∏_{i<n} ∏_{j<m} (1 + α_j β_i T)`.

Induction on `n`: the new variable branches the determinant over vertical strips
(`eDet_succ`), which dual Pieri reassembles (`sum_strips_eq`). -/
theorem dual_cauchy_eDet (α β : ℕ → R) (T : R) (m : ℕ) : ∀ n B : ℕ, n ≤ B →
    ∑ lam ∈ boxParts m B, T ^ (∑ i, lam i) * schurV α m m lam * eDet β n (fun i => (lam i : ℤ)) =
      ∏ i ∈ range n, ∏ j : Fin m, (1 + α j * β i * T)
  | 0, B, _ => by
    rw [prod_range_zero, sum_eq_single (0 : Fin m → ℕ)]
    · rw [eDet_zero_index β (fun _ _ _ => le_rfl), if_pos rfl, schurV_zero_shape]; simp
    · intro lam hl h0
      rw [eDet_zero_index β (mem_boxParts.mp hl).1, if_neg h0, mul_zero]
    · intro h; exact absurd (mem_boxParts.mpr ⟨fun _ _ _ => le_rfl, fun _ => Nat.zero_le _⟩) h
  | n + 1, B, hB => by
    classical
    have IH := dual_cauchy_eDet α β T m n B (by omega)
    -- branch the determinant over vertical strips
    have step1 : ∀ lam ∈ boxParts m B, eDet β (n + 1) (fun i => (lam i : ℤ)) =
        ∑ J ∈ univ.filter (IsVStrip lam), β n ^ J.card *
          eDet β n (fun i => (vsub lam J i : ℤ)) := by
      intro lam hl
      rw [eDet_succ, ← sum_filter_add_sum_filter_not univ (IsVStrip lam),
        sum_eq_zero (s := univ.filter fun J => ¬ IsVStrip lam J) fun J hJ => by
          rw [eDet_eq_zero_of_not_isVStrip β n (mem_boxParts.mp hl).1 (mem_filter.mp hJ).2,
            mul_zero], add_zero]
      refine sum_congr rfl fun J hJ => ?_
      rw [cast_vsub (mem_filter.mp hJ).2.1]
    rw [sum_congr rfl fun lam hl => by rw [step1 lam hl, mul_sum]]
    rw [sum_comm' (t' := univ) (s' := fun J => (boxParts m B).filter fun lam => IsVStrip lam J)
      (by intro lam J; simp [and_comm])]
    -- reindex `λ = μ + 1_J`
    have step2 : ∀ J : Finset (Fin m),
        ∑ lam ∈ (boxParts m B).filter (fun lam => IsVStrip lam J),
          T ^ (∑ i, lam i) * schurV α m m lam *
            (β n ^ J.card * eDet β n (fun i => (vsub lam J i : ℤ))) =
        ∑ mu ∈ (boxParts m B).filter (fun mu => Antitone (mu + ind J)),
          T ^ (∑ i, mu i) * eDet β n (fun i => (mu i : ℤ)) *
            ((β n * T) ^ J.card * schurV α m m (mu + ind J)) := by
      intro J
      rw [← sum_filter_of_ne (s := (boxParts m B).filter (fun mu => Antitone (mu + ind J)))
        (p := fun mu => ∀ i, (mu + ind J) i ≤ B) ?_, filter_filter]
      · refine sum_nbij' (fun lam => vsub lam J) (fun mu => mu + ind J) ?_ ?_ ?_ ?_ ?_
        · intro lam hl
          obtain ⟨hlB, hv⟩ := mem_filter.mp hl
          obtain ⟨hla, hlb⟩ := mem_boxParts.mp hlB
          refine mem_filter.mpr ⟨mem_boxParts.mpr ⟨hv.2, fun i => (Nat.sub_le _ _).trans (hlb i)⟩,
            ?_, ?_⟩ <;> rw [vsub_add_ind hv.1]
          · exact hla
          · exact hlb
        · intro mu hm
          obtain ⟨hmB, ha, hb⟩ := mem_filter.mp hm
          refine mem_filter.mpr ⟨mem_boxParts.mpr ⟨ha, hb⟩, (⟨fun i hi => ?_, ?_⟩ : IsVStrip _ J)⟩
          · simp [ind, hi]
          · rw [vsub_add_ind']; exact (mem_boxParts.mp hmB).1
        · intro lam hl; exact vsub_add_ind (mem_filter.mp hl).2.1
        · intro mu _; exact vsub_add_ind' mu J
        · intro lam hl
          have hv := (mem_filter.mp hl).2
          have hs := sum_vsub_add_card hv.1
          conv_lhs => rw [← vsub_add_ind hv.1]
          rw [vsub_add_ind', sum_add_ind, pow_add, mul_pow]
          ring
      · intro mu hm hne i
        obtain ⟨hmB, ha⟩ := mem_filter.mp hm
        obtain ⟨hma, hmb⟩ := mem_boxParts.mp hmB
        by_contra hc
        have hi : n < mu i := by
          have := hmb i
          simp only [Pi.add_apply, ind] at hc
          split_ifs at hc <;> omega
        exact hne (by rw [eDet_eq_zero_of_lt β hma hi]; ring)
    rw [sum_congr rfl fun J _ => step2 J]
    rw [sum_comm' (t' := boxParts m B)
      (s' := fun mu => univ.filter fun J => Antitone (mu + ind J)) (by intro J mu; simp [and_comm])]
    rw [prod_range_succ, ← IH, sum_mul]
    refine sum_congr rfl fun mu hm => ?_
    rw [← mul_sum, sum_strips_eq α (mem_boxParts.mp hm).1]
    simp only [mul_assoc]
    ring

/-- **The dual Cauchy identity.** For `n ≤ K`, over any commutative ring,

  `Σ_{λ ⊆ m × n} T^{|λ|} s_λ(α₀, …, α_{m−1}) s_{λ'}(β₀, …, β_{n−1}) = ∏_{i<n, j<m} (1 + α_j β_i T)`,

the sum over the partitions `λ` with at most `m` rows and at most `n` columns, `λ'` their
conjugates (`conjV`, with `K` rows). -/
@[frame_pattern]
theorem dual_cauchy (α β : ℕ → R) (T : R) (m n K : ℕ) (hK : n ≤ K) :
    ∑ lam ∈ boxParts m n,
        T ^ (∑ i, lam i) * (schurV α m m lam * schurV β K n (conjV K lam)) =
      ∏ i : Fin n, ∏ j : Fin m, (1 + α j * β i * T) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => ∏ j : Fin m, (1 + α j * β i * T)),
    ← dual_cauchy_eDet α β T m n n le_rfl]
  refine sum_congr rfl fun lam hl => ?_
  obtain ⟨ha, hb⟩ := mem_boxParts.mp hl
  rw [schurV_conjV_eq_eDet β n lam ha fun i => (hb i).trans hK]
  simp only [mul_assoc]

/-- **The dual Cauchy identity at `T = 1`**: `Σ_{λ ⊆ m × n} s_λ(α) s_{λ'}(β) = ∏ (1 + α_j β_i)`. -/
@[frame_pattern]
theorem dual_cauchy_one (α β : ℕ → R) (m n : ℕ) :
    ∑ lam ∈ boxParts m n, schurV α m m lam * schurV β n n (conjV n lam) =
      ∏ i : Fin n, ∏ j : Fin m, (1 + α j * β i) := by
  have h := dual_cauchy α β 1 m n n le_rfl
  simpa using h

end RMT.Symmetric
