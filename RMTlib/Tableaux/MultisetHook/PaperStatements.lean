import RMTlib.Tableaux.MultisetHook.Generating

/-!
# The paper's `q`-series results, stated

The remaining results of Dehaye–Han are identities of `q`-series. They are stated here
coefficient by coefficient, without the analytic part:

* A `q`-series `∑ fₙ qⁿ` **is `exp(∑ aₙ qⁿ)`** (`IsExp f a`) when `f₀ = 1` and
  `n fₙ = ∑_{j=1}^{n} j aⱼ f_{n−j}`. This recursion characterises `exp` (`IsExp.unique`).
  Infinite products `∏_m (1 − c qᵐ)^e` are written as `exp` of their logarithms.
* `sin(kz)` becomes `τ(k) = w^k − w^{−k}` (`tauW`, `w = e^{iz}`), up to the factor `2i`, which
  cancels in every ratio. `sin(tz)` for a parameter `t` becomes `v − v^{−1}` with `v = e^{itz}`,
  an arbitrary nonzero parameter. The weight `1 − sin²(tz)/sin²(hz)` becomes
  `1 − (v − v⁻¹)²/τ(h)²`.

Proved here, in addition to what the other files prove:

* `IsExp.unique`.
* `exists_hook_eq_of_not_core`: a partition that is not a `t`-core has a hook equal to `t`. This
  is the "basic fact" in the proof of Theorem 5: the weight vanishes on non-cores when `v = w^t`.
* `lemma13_iff_macdonaldSpec`: Lemma 13 ⇔ the specialised Macdonald identity (Theorem 11), from
  `lemma13_iff_macdonald`.

Stated, not proved (the paper's derivations are analytic or packaging):
`MacdonaldSpec` (Theorem 11, in the specialised form the paper uses), `Lemma13`, `Lemma14`,
`Theorem5`, `Theorem2`, `Theorem15` (generating-function form; its combinatorial content is
`hanJi_comb`), `Theorem16`, `Corollary6`–`Corollary10`.
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

open Classical

variable {F : Type*} [Field F] [CharZero F]

/-! ### `exp` of a `q`-series, coefficient by coefficient -/

/-- **`∑ fₙ qⁿ = exp(∑_{n≥1} aₙ qⁿ)`**: `f₀ = 1` and `n fₙ = ∑_{j=1}^{n} j aⱼ f_{n−j}`. -/
def IsExp (f a : ℕ → F) : Prop :=
  f 0 = 1 ∧ ∀ n : ℕ, ((n : F) + 1) * f (n + 1) = ∑ j ∈ range (n + 1), ((j : F) + 1) * a (j + 1) * f (n - j)

/-- The recursion determines `f`. -/
theorem IsExp.unique {f g a : ℕ → F} (hf : IsExp f a) (hg : IsExp g a) : f = g := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [hf.1, hg.1]
    · have e1 := hf.2 n; have e2 := hg.2 n
      have : ∑ j ∈ range (n + 1), ((j : F) + 1) * a (j + 1) * f (n - j) =
          ∑ j ∈ range (n + 1), ((j : F) + 1) * a (j + 1) * g (n - j) :=
        sum_congr rfl fun j hj => by rw [ih (n - j) (by rw [mem_range] at hj; omega)]
      have hn : ((n : F) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      exact mul_left_cancel₀ hn (by rw [e1, e2, this])

/-- The logarithm of `∏_{m≥1} (1 − c qᵐ)^e`: `−e ∑_{k ∣ n} cᵏ/k`. -/
def logProd (c e : F) (n : ℕ) : F := -e * ∑ k ∈ n.divisors, c ^ k / k

/-! ### Weights -/

/-- `1 − sin²(tz)/sin²(hz)`, with `sin(tz) ↦ v − v⁻¹` and `sin(hz) ↦ τ(h)`. -/
def sinWeight (w v : F) (h : ℤ) : F := 1 - (v - v⁻¹) ^ 2 / tauW w h ^ 2

/-- `∑_{|λ| = n} ∏_{h ∈ H_r(λ)} g(h)`. -/
def hookSum (n r : ℕ) (g : ℤ → F) : F :=
  ∑ μ ∈ diagrams n, (((hooks μ).filter fun h => (r : ℤ) ∣ h).map g).prod

/-- `∑_{|λ| = n, λ t-core} ∏_{h ∈ H(λ)} g(h)`. -/
def coreSum (n t : ℕ) (g : ℤ → F) : F :=
  ∑ μ ∈ (diagrams n).filter (IsTCore t), ((hooks μ).map g).prod

/-! ### The basic fact of Theorem 5 -/

/-- **A partition that is not a `t`-core has a hook equal to `t`.** -/
theorem exists_hook_eq_of_not_core {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (h : ¬ IsTCore t μ) :
    (t : ℤ) ∈ hooks μ := by
  have hcs := coreStable ht μ
  unfold CoreStable at hcs
  rw [hcs] at h
  push Not at h
  obtain ⟨x, ⟨i, rfl⟩, hn⟩ := h
  obtain ⟨j, hj⟩ := (cover μ _).resolve_left hn
  have hm : (i, j) ∈ μ := (hole_lt_site_iff μ).mp (by omega)
  have := mem_hooks hm
  rwa [hj, sub_sub_cancel] at this

/-! ### Lemma 13 and Macdonald's identity (Theorem 11) -/

/-- The logarithm of the product in Eq. (35):
`∏_m (1 − qᵐ)^{t−1} ∏_{i<t} (1 − y^{t−i} qᵐ)^i (1 − y^{−(t−i)} qᵐ)^i`, `y = w²`. -/
def lemma13Log (t : ℕ) (w : F) (n : ℕ) : F :=
  logProd 1 ((t : F) - 1) n + ∑ i ∈ Ico 1 t,
    (logProd (w ^ (2 * ((t : ℤ) - i))) i n + logProd (w ^ (-2 * ((t : ℤ) - i))) i n)

/-- **Lemma 13** (`t` odd): `∑_{λ t-core} q^{|λ|} ∏_h (1 − sin²(tz)/sin²(hz))` is the product of
Eq. (35). Here `sin(tz) ↦ τ(t)`. -/
def Lemma13 (t : ℕ) (w : F) : Prop :=
  ∃ e, IsExp e (lemma13Log t w) ∧ ∀ n, coreSum n t (fun h => 1 - tauW w t ^ 2 / tauW w h ^ 2) = e n

/-- **Theorem 11, specialised** (the display before Lemma 12, `t = 2t' + 1`):
`∑_{λ t-core} q^{|λ|} ∏_{i<j} sin(u_i z − u_j z) = (−1)^{t'} ∏_k sin^{t−k}(kz) × (35)`. -/
def MacdonaldSpec (t' : ℕ) (w : F) : Prop :=
  ∃ e, IsExp e (lemma13Log (2 * t' + 1) w) ∧ ∀ n,
    ∑ μ ∈ (diagrams n).filter (IsTCore (2 * t' + 1)),
        ∏ p ∈ (univ : Finset (Fin (2 * t' + 1) × Fin (2 * t' + 1))).filter (fun p => p.1 < p.2),
          tauW w (uCoding (2 * t' + 1) μ p.1 - uCoding (2 * t' + 1) μ p.2) =
      (-1) ^ t' * (∏ k ∈ Ico 1 (2 * t' + 1), tauW w k ^ (2 * t' + 1 - k)) * e n

omit [CharZero F] in
theorem sinWeight_eq (w : F) {h t : ℤ} (hh : tauW w h ≠ 0) :
    1 - tauW w t ^ 2 / tauW w h ^ 2 = tauW w (h - t) * tauW w (h + t) / tauW w h ^ 2 := by
  have hw : w ≠ 0 := by
    rintro rfl; apply hh; simp only [tauW]
    rcases eq_or_ne h 0 with rfl | h0
    · simp
    · rw [zero_zpow h (by omega), zero_zpow (-h) (by omega), sub_zero]
  field_simp
  simp only [tauW, zpow_sub₀ hw, zpow_add₀ hw, zpow_neg]
  field_simp
  ring

omit [CharZero F] in
/-- **Lemma 13 ⇔ the specialised Macdonald identity.** -/
theorem lemma13_iff_macdonaldSpec (t' : ℕ) {w : F} (hw : ∀ k : ℤ, k ≠ 0 → w ^ k ≠ w ^ (-k)) :
    Lemma13 (2 * t' + 1) w ↔ MacdonaldSpec t' w := by
  have hweights : ∀ n, coreSum n (2 * t' + 1) (fun h => 1 - tauW w (2 * t' + 1 : ℕ) ^ 2 /
      tauW w h ^ 2) = ∑ μ ∈ (diagrams n).filter (IsTCore (2 * t' + 1)),
        ((hooks μ).map fun h => tauW w (h - (2 * t' + 1 : ℕ)) * tauW w (h + (2 * t' + 1 : ℕ)) /
          tauW w h ^ 2).prod := fun n => by
    refine sum_congr rfl fun μ hμ => congrArg _ (Multiset.map_congr rfl fun h hh => ?_)
    have := one_le_of_mem_hooks hh
    exact sinWeight_eq w (sub_ne_zero.mpr (hw h (by omega)))
  constructor
  · rintro ⟨e, he, hsum⟩
    exact ⟨e, he, (lemma13_iff_macdonald hw e).mp fun n => (hweights n).symm.trans (hsum n)⟩
  · rintro ⟨e, he, hsum⟩
    exact ⟨e, he, fun n => (hweights n).trans ((lemma13_iff_macdonald hw e).mpr hsum n)⟩

/-! ### Lemma 14, Theorems 5 and 2 -/

/-- The logarithm `∑_k qᵏ/(k(1 − qᵏ)) (1 − sin²(tkz)/sin²(kz))`, with `sin(tkz) ↦ vᵏ − v⁻ᵏ`. -/
def thm5Log (w v : F) (n : ℕ) : F :=
  ∑ k ∈ n.divisors, (1 - (v ^ k - v⁻¹ ^ k) ^ 2 / tauW w k ^ 2) / k

/-- **Lemma 14** (`t` odd): the core sum is `exp ∑_k qᵏ/(k(1−qᵏ)) (1 − sin²(tkz)/sin²(kz))`. -/
def Lemma14 (t : ℕ) (w : F) : Prop :=
  ∃ e, IsExp e (thm5Log w (w ^ t)) ∧
    ∀ n, coreSum n t (fun h => 1 - tauW w t ^ 2 / tauW w h ^ 2) = e n

/-- **Theorem 5** (`r = 1`): `∑_λ q^{|λ|} ∏_h (1 − sin²(tz)/sin²(hz))
= exp ∑_k qᵏ/(k(1−qᵏ)) (1 − sin²(tkz)/sin²(kz))`, for every parameter `v = e^{itz}`. -/
def Theorem5 (w v : F) : Prop :=
  ∃ e, IsExp e (thm5Log w v) ∧ ∀ n, hookSum n 1 (sinWeight w v) = e n

/-- The logarithm of Theorem 2:
`∑_k (qᵏ/(k(1−qᵏ)) − r q^{rk}/(k(1−q^{rk})) sin²(tkz)/sin²(rkz))`. -/
def thm2Log (r : ℕ) (w v : F) (n : ℕ) : F :=
  ∑ k ∈ n.divisors, (1 : F) / k -
    if (r : ℕ) ∣ n then ∑ k ∈ (n / r).divisors, (r : F) / k * ((v ^ k - v⁻¹ ^ k) ^ 2 /
      tauW w (r * k) ^ 2) else 0

/-- **Theorem 2**: `∑_λ q^{|λ|} ∏_{h ∈ H_r(λ)} (1 − sin²(tz)/sin²(hz)) = exp(thm2Log)`. -/
def Theorem2 (r : ℕ) (w v : F) : Prop :=
  ∃ e, IsExp e (thm2Log r w v) ∧ ∀ n, hookSum n r (sinWeight w v) = e n

/-! ### Theorem 15 (Han–Ji) -/

/-- The logarithm of `∏_k (1 − q^{rk})^r/(1 − qᵏ)`, the generating function of `r`-cores. -/
def coreLog (r : ℕ) (n : ℕ) : F :=
  ∑ k ∈ n.divisors, (1 : F) / k - if r ∣ n then ∑ k ∈ (n / r).divisors, (r : F) / k else 0

/-- **Theorem 15 (Han–Ji, the multiplication theorem)**: with `f_α(q) = ∑_λ q^{|λ|} ∏_h ρ(αh)`,
`∑_λ q^{|λ|} x^{#H_r(λ)} ∏_{h ∈ H_r(λ)} ρ(h) = f_r(x q^r)^r ∏_k (1 − q^{rk})^r/(1 − qᵏ)`,
coefficient by coefficient. Its combinatorial content is `hanJi_comb`. -/
def Theorem15 (r : ℕ) (x : F) (ρf : ℤ → F) : Prop :=
  ∃ c, IsExp c (coreLog r) ∧ ∀ n,
    ∑ μ ∈ diagrams n, x ^ ((hooks μ).filter (fun h => (r : ℤ) ∣ h)).card *
        (((hooks μ).filter (fun h => (r : ℤ) ∣ h)).map ρf).prod =
      ∑ a ∈ (range (n + 1)).filter (fun a => r ∣ n - a), c a * x ^ ((n - a) / r) *
        ∑ b ∈ (Fintype.piFinset fun _ : Fin r => range (n + 1)).filter
            (fun b => ∑ ρ, b ρ = (n - a) / r),
          ∏ ρ, ∑ μ ∈ diagrams (b ρ), ((hooks μ).map fun h => ρf (r * h)).prod

/-! ### Theorem 16 (the hook-content formula) -/

/-- Semistandard fillings of `λ` with entries `< n`: weakly increasing along rows, strictly down
columns. -/
def ssyt (μ : YoungDiagram) (n : ℕ) : Finset (μ.cells → Fin n) :=
  univ.filter fun T => ∀ c d : μ.cells,
    ((c.1.1 = d.1.1 ∧ c.1.2 ≤ d.1.2) → T c ≤ T d) ∧ ((c.1.2 = d.1.2 ∧ c.1.1 < d.1.1) → T c < T d)

/-- **Theorem 16 (hook-content formula)**: `s_λ(1, p, …, p^{n−1}) = p^{b(λ)} ∏_□ (1 − p^{n+c})/(1 − p^h)`,
`b(λ) = ∑_i i λ_i`, `c = j − i`. -/
def Theorem16 (μ : YoungDiagram) (n : ℕ) (p : F) : Prop :=
  ∑ T ∈ ssyt μ n, p ^ (∑ c, (T c : ℕ)) =
    p ^ (∑ c ∈ μ.cells, c.1) * ∏ c ∈ μ.cells,
      (1 - p ^ ((n : ℤ) + c.2 - c.1)) / (1 - p ^ hook μ c)

/-! ### Corollaries 6–10 -/

/-- **Corollary 6**: `∑_λ q^{|λ|} = ∏_m 1/(1 − qᵐ)`. -/
def Corollary6 : Prop :=
  ∃ e, IsExp e (logProd (1 : F) (-1)) ∧ ∀ n, ((diagrams n).card : F) = e n

/-- **Corollary 7 (Nekrasov–Okounkov, Eq. (22))**: `∑_λ q^{|λ|} ∏_h (1 − β/h²) = ∏_m (1 − qᵐ)^{β−1}`. -/
def Corollary7 (β : F) : Prop :=
  ∃ e, IsExp e (logProd 1 (β - 1)) ∧ ∀ n, hookSum n 1 (fun h => 1 - β / (h : F) ^ 2) = e n

/-- **Corollary 8 (Eq. (24))**: `∑_λ q^{|λ|} ∏_h 1/(4 sin²(hz)) = exp ∑_k qᵏ/(4k sin²(kz))`;
`4 sin²(hz) ↦ −τ(h)²`. -/
def Corollary8 (w : F) : Prop :=
  ∃ e, IsExp e (fun n : ℕ => -1 / ((n : F) * tauW w n ^ 2)) ∧
    ∀ n, hookSum n 1 (fun h => -1 / tauW w h ^ 2) = e n

/-- **Corollary 9**: `∑_λ q^{|λ|} ∏_h cot²(zh)
= exp ∑_k (q^{2k−1} cot²((2k−1)z)/((2k−1)(1+q^{2k−1})) + q^{2k}/(2k(1−q^{2k})))`;
`cot(hz) ↦ i(wʰ + w⁻ʰ)/τ(h)`. -/
def Corollary9 (w : F) : Prop :=
  ∃ e, IsExp e (fun n : ℕ => ∑ k ∈ n.divisors,
      if k % 2 = 1 then (-1 : F) ^ (n / k - 1) * (-(w ^ (k : ℤ) + w ^ (-(k : ℤ))) ^ 2 /
        tauW w k ^ 2) / (k : F) else (1 : F) / k) ∧
    ∀ n, hookSum n 1 (fun h => -(w ^ h + w ^ (-h)) ^ 2 / tauW w h ^ 2) = e n

/-- **Corollary 10 (Jacobi's triple product, Eq. (27))**:
`∏_{n≥0} (1 + a x^{n+1})(1 + xⁿ/a)(1 − x^{n+1}) = ∑_{n∈ℤ} aⁿ x^{n(n+1)/2}`. The `n = 0` factor
`1 + 1/a` is taken out; the rest is `exp` of its logarithm. -/
def Corollary10 (a : F) : Prop :=
  ∃ e, IsExp e (fun N => logProd (-a) 1 N + logProd (-a⁻¹) 1 N + logProd 1 1 N) ∧
    ∀ N : ℕ, (1 + a⁻¹) * e N =
      ∑ n ∈ Icc (-(N : ℤ) - 1) N, if n * (n + 1) = 2 * N then a ^ n else 0

end

end RMT.MultisetHook
