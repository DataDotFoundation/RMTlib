import RMTlib.Symmetric.JacobiTrudi

/-!
# Schur polynomials as weighted sums over Gelfand–Tsetlin patterns

A **Gelfand–Tsetlin pattern** of shape `λ : Fin N → ℕ` with `m` levels is a chain of interlacing
vectors

  `0 = p₀ ≺ p₁ ≺ ⋯ ≺ p_m = λ`,   `p_k ≺ p_{k+1}` meaning `(p_{k+1})_{t+1} ≤ (p_k)_t ≤ (p_{k+1})_t`

(`RMT.Weyl.GTStep (p (k+1)) (p k)`). Its weight at values `a₀, a₁, …` is
`∏_{k < m} a_k ^ (|p_{k+1}| − |p_k|)`. This file proves that the Schur polynomial is the total
weight of the patterns (`sum_gtPatterns_eq_schurV`, `sum_gtPatterns_eq_det`):

  `s_λ(a₀, …, a_{m−1}) = Σ_{p ∈ GT(λ, m)} ∏_k a_k ^ (|p_{k+1}| − |p_k|) = det (h_{λ_i − i + j}(a))`.

The set of patterns is built level by level (`gtPatterns`, characterised by `mem_gtPatterns`),
so the identity is the branching rule `RMT.Symmetric.schurV_succ` iterated: one kernel
`Q(λ, μ; t) = t^{|λ| − |μ|} · 1[μ ≺ λ]` per level.

This is the **finite-place instance of a pattern formulation of spherical Whittaker
functions**: with `a = ` Satake parameters, `δ^{−1/2}(ϖ^λ) · W(ϖ^λ) / W(1)` is this sum
(Shintani; the bridge `RMTlibBridge.Shintani` states it for the RH formalisation's
`GlobalTheory.JSW.sphW`). The archimedean analogue (Givental's integral over the same
interlacing levels, with a soft kernel) is not formalised; see `bridge/links/target3-shintani.md`.

## Main results

* `IsGTPattern`, `gtWeight`, `gtPatterns`, `mem_gtPatterns`.
* `sum_gtPatterns_eq_schurV`: Schur polynomial = weighted GT-pattern sum.
* `sum_gtPatterns_eq_det`: weighted GT-pattern sum = Jacobi–Trudi determinant.
-/

open Finset Matrix

namespace RMT.Symmetric

variable {N : ℕ}

/-- `p : Fin (m + 1) → (Fin N → ℕ)` is a Gelfand–Tsetlin pattern of shape `λ` with `m` levels:
`p 0 = 0`, `p m = λ`, and each level interlaces into the next. -/
def IsGTPattern (m : ℕ) (lam : Fin N → ℕ) (p : Fin (m + 1) → Fin N → ℕ) : Prop :=
  p 0 = 0 ∧ p (Fin.last m) = lam ∧ ∀ k : Fin m, Weyl.GTStep (p k.succ) (p k.castSucc)

/-- The weight `∏_{k < m} a_k ^ (|p_{k+1}| − |p_k|)` of a pattern. -/
def gtWeight {R : Type*} [CommMonoid R] (a : ℕ → R) (m : ℕ) (p : Fin (m + 1) → Fin N → ℕ) : R :=
  ∏ k : Fin m, a k ^ (∑ i, p k.succ i - ∑ i, p k.castSucc i)

/-- The Gelfand–Tsetlin patterns of shape `λ` with `m` levels, built level by level. -/
noncomputable def gtPatterns : (m : ℕ) → (Fin N → ℕ) → Finset (Fin (m + 1) → Fin N → ℕ)
  | 0, lam => by classical exact if lam = 0 then {fun _ => 0} else ∅
  | m + 1, lam => by
    classical exact (interl lam).biUnion fun mu => (gtPatterns m mu).image fun p => Fin.snoc p lam

/-- The top level of a pattern in `gtPatterns m λ` is `λ`. -/
theorem last_of_mem_gtPatterns : ∀ {m : ℕ} {lam : Fin N → ℕ} {p : Fin (m + 1) → Fin N → ℕ},
    p ∈ gtPatterns m lam → p (Fin.last m) = lam
  | 0, lam, p, h => by
    classical
    unfold gtPatterns at h
    split_ifs at h with h0
    · rw [Finset.mem_singleton] at h; subst h; exact h0.symm
    · simp at h
  | m + 1, lam, p, h => by
    classical
    unfold gtPatterns at h
    obtain ⟨mu, -, hp⟩ := Finset.mem_biUnion.mp h
    obtain ⟨p', -, rfl⟩ := Finset.mem_image.mp hp
    simp

/-- **`gtPatterns m λ` is the set of Gelfand–Tsetlin patterns of shape `λ` with `m` levels.** -/
theorem mem_gtPatterns : ∀ (m : ℕ) (lam : Fin N → ℕ) (p : Fin (m + 1) → Fin N → ℕ),
    p ∈ gtPatterns m lam ↔ IsGTPattern m lam p
  | 0, lam, p => by
    classical
    unfold gtPatterns IsGTPattern
    constructor
    · intro h
      split_ifs at h with h0
      · rw [Finset.mem_singleton] at h; subst h; exact ⟨rfl, h0.symm, fun k => k.elim0⟩
      · simp at h
    · rintro ⟨h0, hl, -⟩
      have hl' : p 0 = lam := hl
      have : lam = 0 := hl'.symm.trans h0
      rw [if_pos this, Finset.mem_singleton]
      funext k
      have hk : k = 0 := Fin.ext (by have := k.2; omega)
      rw [hk, h0]
  | m + 1, lam, p => by
    classical
    unfold gtPatterns
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨mu, hmu, hp⟩
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨h0, hl, hs⟩ := (mem_gtPatterns m mu p').mp hp'
      refine ⟨?_, by simp, fun k => ?_⟩
      · rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc from rfl, Fin.snoc_castSucc, h0]
      · refine Fin.lastCases ?_ (fun k => ?_) k
        · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hl]
          exact mem_interl.mp hmu
        · rw [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hs k
    · rintro ⟨h0, hl, hs⟩
      refine ⟨p (Fin.last m).castSucc, ?_, Finset.mem_image.mpr ⟨Fin.init p, ?_, ?_⟩⟩
      · have := hs (Fin.last m)
        rw [Fin.succ_last, hl] at this
        exact mem_interl.mpr this
      · refine (mem_gtPatterns m _ _).mpr ⟨?_, rfl, fun k => ?_⟩
        · exact h0
        · have := hs k.castSucc
          show Weyl.GTStep (p k.succ.castSucc) (p k.castSucc.castSucc)
          rwa [← Fin.succ_castSucc]
      · rw [← hl]; exact Fin.snoc_init_self p

/-- Weight of a pattern extended by one level. -/
theorem gtWeight_snoc {R : Type*} [CommMonoid R] (a : ℕ → R) (m : ℕ) (p : Fin (m + 1) → Fin N → ℕ)
    (lam : Fin N → ℕ) :
    gtWeight a (m + 1) (Fin.snoc p lam : Fin (m + 2) → Fin N → ℕ)
      = a m ^ (∑ i, lam i - ∑ i, p (Fin.last m) i) * gtWeight a m p := by
  rw [gtWeight, Fin.prod_univ_castSucc, mul_comm, gtWeight]
  congr 1
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last]
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [Fin.val_castSucc, ← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- **Schur polynomials are weighted sums over Gelfand–Tsetlin patterns**:
`s_λ(a₀, …, a_{m−1}) = Σ_{p ∈ GT(λ, m)} ∏_k a_k ^ (|p_{k+1}| − |p_k|)`, for every `λ : Fin N → ℕ`
(no antitonicity hypothesis: both sides satisfy the same branching rule, `schurV_succ`). -/
theorem sum_gtPatterns_eq_schurV {R : Type*} [CommRing R] (a : ℕ → R) :
    ∀ (m : ℕ) (lam : Fin N → ℕ), ∑ p ∈ gtPatterns m lam, gtWeight a m p = schurV a N m lam
  | 0, lam => by
    classical
    rw [schurV_zero]
    unfold gtPatterns
    split_ifs with h
    · simp [gtWeight]
    · simp
  | m + 1, lam => by
    classical
    rw [schurV_succ]
    unfold gtPatterns
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun mu _ => ?_
      rw [Finset.sum_image (fun p _ q _ h => by
        have := congrArg Fin.init h
        simpa [Fin.init_snoc] using this)]
      rw [← sum_gtPatterns_eq_schurV a m mu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [gtWeight_snoc, last_of_mem_gtPatterns hp]
    · intro mu _ nu _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp hq
      obtain ⟨p₁, h₁, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨p₂, h₂, he⟩ := Finset.mem_image.mp hq
      apply hne
      have := congrArg (fun f : Fin (m + 2) → Fin N → ℕ => f (Fin.last m).castSucc) he
      simp only [Fin.snoc_castSucc] at this
      rw [← last_of_mem_gtPatterns h₁, ← last_of_mem_gtPatterns h₂, this]

/-- **Weighted GT-pattern sum = Jacobi–Trudi determinant** (`schurV_eq_det`), for antitone `λ`. -/
theorem sum_gtPatterns_eq_det {R : Type*} [CommRing R] (a : ℕ → R) (m : ℕ) (lam : Fin N → ℕ)
    (hl : Antitone lam) : ∑ p ∈ gtPatterns m lam, gtWeight a m p = det (jtMat a m lam) := by
  rw [sum_gtPatterns_eq_schurV, schurV_eq_det a m lam hl]

/-- At `a = 1` every pattern has weight `1`: the Schur value counts patterns. -/
theorem card_gtPatterns {R : Type*} [CommRing R] (m : ℕ) (lam : Fin N → ℕ) :
    ((gtPatterns m lam).card : R) = schurV (fun _ => (1 : R)) N m lam := by
  rw [← sum_gtPatterns_eq_schurV]
  simp [gtWeight]

end RMT.Symmetric
