import RMTlib.Symmetric.WeightedCauchy

/-!
# Chains of theta lifts at `∞`: the smallest rank sets the cut (W5)

Companion to `bridge/links/virasoro-briefing.md` (§11); checks in `bridge/scripts/lift_chains.py`. GRH-free.

Compose Cauchy kernels `Σ_ν s_ν(x) s_ν(y)` through middle spaces, contracting each middle copy with the Fock
pairing at its rank, `⟨s_λ, s_μ⟩_N = δ_{λμ} ∏_{□∈λ} (N + c)`. A chain through ranks `N_1, …, N_r` then has
weight `∏_j ∏_{□∈ν} (N_j + c)` on `s_ν ⊗ s_ν`. A link of dual-Cauchy type `Σ s_ν ⊗ s_{ν'}` (the ω-twin) passes
`ν'` to the middle space, so its weight is `∏_□ (M + c(ν')) = ∏_{□∈ν} (M − c)`.

* `chain_eq_zero_iff`: the bosonic chain weight vanishes iff `ℓ(ν) > min_j N_j`. **The smallest rank sets the
  cut**, the analogue of the first-occurrence / stable-range condition.
* `chain_sub_eq_zero_iff` (twin): the fermionic chain weight vanishes iff `ν_1 > min_j M_j`.
* `alt_chain_ne_zero_iff`: an alternating Sym/Λ chain is supported exactly on the box `ℓ(ν) ≤ min N_j`,
  `ν_1 ≤ min M_j`, the box of Howe's skew duality.

Computed only (`lift_chains.py`): the semigroup law `K_T ∘ K_{T'} = K_{TT'}` at a finite place, `K^ω ∘ K^ω = K`,
and `Δ^m` moving charges in arithmetic progression.
-/

open YoungDiagram

namespace RMT.Symmetric

variable {ι : Type*}

/-- **The smallest rank sets the cut**: `∏_{j∈s} ∏_{□∈μ} (N_j + c) = 0` iff `μ` has more than `min_j N_j` rows. -/
theorem chain_eq_zero_iff (s : Finset ι) (hs : s.Nonempty) (N : ι → ℕ) (μ : YoungDiagram) :
    ∏ j ∈ s, contentProd (fun z : ℤ => (N j : ℤ) + z) μ = 0 ↔ (s.inf' hs N, 0) ∈ μ := by
  rw [Finset.prod_eq_zero_iff]
  simp only [contentProd_nat_add_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    exact μ.up_left_mem (Finset.inf'_le N hj) le_rfl h
  · intro h
    obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' hs N
    exact ⟨j, hj, he ▸ h⟩

/-- **The fermionic twin**: `∏_{j∈s} ∏_{□∈μ} (M_j − c) = 0` iff `μ` has more than `min_j M_j` columns. -/
theorem chain_sub_eq_zero_iff (s : Finset ι) (hs : s.Nonempty) (M : ι → ℕ) (μ : YoungDiagram) :
    ∏ j ∈ s, contentProd (fun z : ℤ => (M j : ℤ) - z) μ = 0 ↔ (0, s.inf' hs M) ∈ μ := by
  rw [Finset.prod_eq_zero_iff]
  simp only [contentProd_nat_sub_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    exact μ.up_left_mem le_rfl (Finset.inf'_le M hj) h
  · intro h
    obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' hs M
    exact ⟨j, hj, he ▸ h⟩

/-- **An alternating Sym/Λ chain is supported on a box**: the weight is nonzero iff `μ` fits in the
`min N × min M` rectangle. -/
theorem alt_chain_ne_zero_iff {κ : Type*} (s : Finset ι) (t : Finset κ) (hs : s.Nonempty) (ht : t.Nonempty)
    (N : ι → ℕ) (M : κ → ℕ) (μ : YoungDiagram) :
    (∏ j ∈ s, contentProd (fun z : ℤ => (N j : ℤ) + z) μ) *
        (∏ j ∈ t, contentProd (fun z : ℤ => (M j : ℤ) - z) μ) ≠ 0 ↔
      (s.inf' hs N, 0) ∉ μ ∧ (0, t.inf' ht M) ∉ μ := by
  rw [mul_ne_zero_iff, Ne, Ne, chain_eq_zero_iff s hs, chain_sub_eq_zero_iff t ht]

end RMT.Symmetric
