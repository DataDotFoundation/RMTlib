import RMTlib.Symmetric.GTSum

/-!
# q-Whittaker polynomials as weighted sums over Gelfand–Tsetlin patterns

The **q-Whittaker polynomial** `P_λ(a₀, …, a_{m−1}; q)` (Macdonald's `P_λ(x; q, t)` at `t = 0`)
is defined here by its branching rule, one level at a time:

  `P_λ(a₀, …, a_m; q) = Σ_{μ ≺ λ} ψ_{λ/μ}(q) · a_m ^ (|λ| − |μ|) · P_μ(a₀, …, a_{m−1}; q)`,
  `ψ_{λ/μ}(q) = ∏_i [λ_i − λ_{i+1} choose λ_i − μ_i]_q`   (`λ_N := 0`),

with `[n choose k]_q` the Gaussian binomial (`qBinom`, by q-Pascal). Unfolded, it is a sum over
Gelfand–Tsetlin patterns with one q-binomial weight per level (`sum_gtPatterns_qWeight`). It agrees
with Gerasimov–Lebedev–Oblezin's q-deformed `gl_{ℓ+1}`-Whittaker function (arXiv:1101.4567,
Thm 1.1; arXiv:0803.0145, Thm 2.1) up to the factor `∏_{i ≤ ℓ} (q; q)_{λ_i − λ_{i+1}}`
(an expansion of the q-binomials into q-factorials; not formalised).

## Main results

* `qWhittV_zero_q`: **at `q = 0` the q-Whittaker polynomial is the Schur polynomial `schurV`**,
  hence the GT-pattern sum of `GTSum.lean` and the Jacobi–Trudi determinant
  (`qWhittV_zero_q_eq_det`). This is the member of the family that the RH formalisation's
  Shintani formula uses at every finite place (bridge `RMTlibBridge.QWhittaker`).
* `qWhittV_one_q_one_row`: at `q = 1` (no scaling) the one-row polynomial is `(a₀ + ⋯ + a_{m−1})^n`,
  the degenerate end `P_λ(x; 1, 0) = e_{λ'}(x)` in the one-row case: the literal value `q = 1`
  is *not* the archimedean member; that is the scaled limit `q = e^{−ε}`, `ε → 0`.
* `schurV_principal_one_row`: **principal specialisation** `h_n(1, q, …, q^m) = [m + n choose m]_q`.
  As `m → ∞` this is `1 / (q; q)_n`, the coefficient of the one-variable q-Whittaker Cauchy
  kernel `1/(xy; q)_∞`. So the q-Whittaker Cauchy kernel is the Schur (finite-place) Cauchy kernel
  with one side principally specialised, `∏_{i,j} 1/(x_i y_j; q)_∞ = ∏_{n ≥ 0} ∏_{i,j} (1 − x_i y_j q^n)⁻¹`.
* `qPoch_mul_qBinom`: `(q; q)_n [m + n choose m]_q = (q^{m+1}; q)_n` (Euler, finite form).
* `prod_qPoch_duplication`: `(T; q)_{2M} = (T; q²)_M (qT; q²)_M`, the q-form of
  `Γ_ℂ(s) = Γ_ℝ(s) Γ_ℝ(s + 1)` (real versus complex places).
* `qBinom_zero_q`, `qBinom_one_q`, `qBinom_self`, `qBinom_eq_zero_of_lt`, `qBinom_succ_right_sum`.
-/

open Finset

namespace RMT.Symmetric

section QBinom

variable {R : Type*} [CommSemiring R]

/-- The **Gaussian binomial coefficient** `[n choose k]_q`, by the q-Pascal rule
`[n+1, k+1] = [n, k] + q^{k+1} [n, k+1]`. -/
def qBinom (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)

@[simp] theorem qBinom_zero_right (q : R) (n : ℕ) : qBinom q n 0 = 1 := by cases n <;> rfl

@[simp] theorem qBinom_zero_succ (q : R) (k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl

/-- q-Pascal. -/
theorem qBinom_succ_succ (q : R) (n k : ℕ) :
    qBinom q (n + 1) (k + 1) = qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl

/-- `[n choose k]_q = 0` for `n < k`. -/
theorem qBinom_eq_zero_of_lt (q : R) : ∀ {n k : ℕ}, n < k → qBinom q n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q (by omega : n < k),
      qBinom_eq_zero_of_lt q (by omega : n < k + 1)]
    simp

/-- `[n choose n]_q = 1`. -/
@[simp] theorem qBinom_self (q : R) : ∀ n : ℕ, qBinom q n n = 1
  | 0 => rfl
  | n + 1 => by rw [qBinom_succ_succ, qBinom_self q n, qBinom_eq_zero_of_lt q (by omega)]; simp

/-- At `q = 0` the Gaussian binomial is the indicator of `k ≤ n`. -/
theorem qBinom_zero_q : ∀ n k : ℕ, qBinom (0 : R) n k = if k ≤ n then 1 else 0
  | n, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, k + 1 => by
    rw [qBinom_succ_succ, qBinom_zero_q n k, zero_pow (Nat.succ_ne_zero k), zero_mul, add_zero]
    by_cases h : k ≤ n
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-- At `q = 1` the Gaussian binomial is the binomial coefficient. -/
theorem qBinom_one_q : ∀ n k : ℕ, qBinom (1 : R) n k = n.choose k
  | n, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, k + 1 => by
    rw [qBinom_succ_succ, qBinom_one_q n k, qBinom_one_q n (k + 1), Nat.choose_succ_succ]
    push_cast; ring

/-- q-Pascal iterated in the upper index:
`[m+1+n choose m+1]_q = Σ_{j ≤ n} q^{(m+1)(n−j)} [m+j choose m]_q`. -/
theorem qBinom_succ_right_sum (q : R) (m : ℕ) : ∀ n : ℕ,
    qBinom q (m + 1 + n) (m + 1)
      = ∑ j ∈ range (n + 1), q ^ ((m + 1) * (n - j)) * qBinom q (m + j) m
  | 0 => by simp
  | n + 1 => by
    rw [show m + 1 + (n + 1) = (m + 1 + n) + 1 by omega, qBinom_succ_succ,
      qBinom_succ_right_sum q m n, Finset.sum_range_succ _ (n + 1), Finset.mul_sum, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj := Finset.mem_range.mp hj
      rw [← mul_assoc, ← pow_add]
      congr 2
      rw [show n + 1 - j = (n - j) + 1 by omega]; ring
    · simp [show m + 1 + n = m + (n + 1) by omega]

end QBinom

variable {N : ℕ} {R : Type*} [CommRing R]

/-- `λ_{i+1}`, with `λ_N := 0`. -/
def nextPart (lam : Fin N → ℕ) (i : Fin N) : ℕ :=
  if h : i.val + 1 < N then lam ⟨i.val + 1, h⟩ else 0

/-- The **q-Whittaker branching coefficient** `ψ_{λ/μ}(q) = ∏_i [λ_i − λ_{i+1} choose λ_i − μ_i]_q`
(Macdonald's `ψ_{λ/μ}(q, t)` at `t = 0`, for a horizontal strip `λ/μ`). -/
def qBranch (q : R) (lam mu : Fin N → ℕ) : R :=
  ∏ i, qBinom q (lam i - nextPart lam i) (lam i - mu i)

/-- The **q-Whittaker polynomial** `P_λ(a₀, …, a_{m−1}; q)`, by the branching rule
`P_λ(a₀, …, a_m) = Σ_{μ ≺ λ} ψ_{λ/μ}(q) a_m^{|λ| − |μ|} P_μ(a₀, …, a_{m−1})`. -/
noncomputable def qWhittV (q : R) (a : ℕ → R) (N : ℕ) : ℕ → (Fin N → ℕ) → R
  | 0, lam => if lam = 0 then 1 else 0
  | m + 1, lam => ∑ mu ∈ interl lam,
      qBranch q lam mu * a m ^ (∑ i, lam i - ∑ i, mu i) * qWhittV q a N m mu

/-- The q-weight `∏_k ψ_{p_{k+1}/p_k}(q)` of a Gelfand–Tsetlin pattern. -/
def qGTWeight (q : R) (m : ℕ) (p : Fin (m + 1) → Fin N → ℕ) : R :=
  ∏ k : Fin m, qBranch q (p k.succ) (p k.castSucc)

theorem qGTWeight_snoc (q : R) (m : ℕ) (p : Fin (m + 1) → Fin N → ℕ) (lam : Fin N → ℕ) :
    qGTWeight q (m + 1) (Fin.snoc p lam : Fin (m + 2) → Fin N → ℕ)
      = qBranch q lam (p (Fin.last m)) * qGTWeight q m p := by
  rw [qGTWeight, Fin.prod_univ_castSucc, mul_comm, qGTWeight]
  congr 1
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- **q-Whittaker polynomials are q-weighted sums over Gelfand–Tsetlin patterns**:
`P_λ(a; q) = Σ_{p ∈ GT(λ, m)} ∏_k a_k^{|p_{k+1}| − |p_k|} · ∏_k ψ_{p_{k+1}/p_k}(q)`. -/
theorem sum_gtPatterns_qWeight (q : R) (a : ℕ → R) :
    ∀ (m : ℕ) (lam : Fin N → ℕ),
      ∑ p ∈ gtPatterns m lam, gtWeight a m p * qGTWeight q m p = qWhittV q a N m lam
  | 0, lam => by
    classical
    unfold gtPatterns qWhittV
    split_ifs with h
    · simp [gtWeight, qGTWeight]
    · simp
  | m + 1, lam => by
    classical
    unfold gtPatterns
    rw [qWhittV, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun mu _ => ?_
      rw [Finset.sum_image (fun p _ q _ h => by
        have := congrArg Fin.init h
        simpa [Fin.init_snoc] using this)]
      rw [← sum_gtPatterns_qWeight q a m mu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [gtWeight_snoc, qGTWeight_snoc, last_of_mem_gtPatterns hp]
      ring
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

/-- On an interlacing pair the branching coefficient at `q = 0` is `1`. -/
theorem qBranch_zero_q {lam mu : Fin N → ℕ} (h : Weyl.GTStep lam mu) :
    qBranch (0 : R) lam mu = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have hn : nextPart lam i ≤ mu i := by
    unfold nextPart
    split_ifs with h'
    · exact h.1 i ⟨i.val + 1, h'⟩ rfl
    · exact Nat.zero_le _
  rw [qBinom_zero_q, if_pos (by omega)]

/-- **At `q = 0` the q-Whittaker polynomial is the Schur polynomial.** -/
theorem qWhittV_zero_q (a : ℕ → R) : ∀ (m : ℕ) (lam : Fin N → ℕ),
    qWhittV (0 : R) a N m lam = schurV a N m lam
  | 0, lam => by rw [schurV_zero, qWhittV]
  | m + 1, lam => by
    rw [qWhittV, schurV_succ]
    refine Finset.sum_congr rfl fun mu hmu => ?_
    rw [qBranch_zero_q (mem_interl.mp hmu), qWhittV_zero_q a m mu, one_mul]

/-- At `q = 0`: q-Whittaker = Jacobi–Trudi determinant (antitone `λ`). -/
theorem qWhittV_zero_q_eq_det (a : ℕ → R) (m : ℕ) (lam : Fin N → ℕ) (hl : Antitone lam) :
    qWhittV (0 : R) a N m lam = Matrix.det (jtMat a m lam) := by
  rw [qWhittV_zero_q, schurV_eq_det a m lam hl]

/-! ### One row -/

/-- For one row, the shapes interlacing `(n)` are `(j)`, `j ≤ n`. -/
theorem sum_interl_one (lam : Fin 1 → ℕ) (f : (Fin 1 → ℕ) → R) :
    ∑ mu ∈ interl lam, f mu = ∑ j ∈ range (lam 0 + 1), f (fun _ => j) := by
  refine Finset.sum_nbij' (fun mu => mu 0) (fun j _ => j) (fun mu hmu => ?_) (fun j hj => ?_)
    (fun mu _ => ?_) (fun j _ => rfl) (fun mu _ => ?_)
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((mem_interl.mp hmu).2 0))
  · refine mem_interl.mpr ⟨fun l j h => absurd h (by omega), fun t => ?_⟩
    rw [Subsingleton.elim t 0]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  · funext i; rw [Subsingleton.elim i 0]
  · congr 1; funext i; rw [Subsingleton.elim i 0]

/-- The one-row branching coefficient: `ψ_{(n)/(j)}(q) = [n choose n − j]_q`. -/
theorem qBranch_one_row (q : R) (n j : ℕ) :
    qBranch q (fun _ : Fin 1 => n) (fun _ => j) = qBinom q n (n - j) := by
  simp [qBranch, nextPart]

/-- **At `q = 1` the one-row q-Whittaker polynomial is `(a₀ + ⋯ + a_{m−1})^n`** (`= e_1^n`,
the one-row case of `P_λ(x; 1, 0) = e_{λ'}(x)`): the unscaled value `q = 1` is degenerate. -/
theorem qWhittV_one_q_one_row (a : ℕ → R) : ∀ m n : ℕ,
    qWhittV (1 : R) a 1 m (fun _ => n) = (∑ k ∈ range m, a k) ^ n
  | 0, n => by
    cases n with
    | zero => rw [qWhittV, if_pos (by funext i; rfl)]; simp
    | succ n =>
      rw [qWhittV, if_neg (fun h => by simpa using congrFun h 0)]
      simp
  | m + 1, n => by
    rw [qWhittV, sum_interl_one]
    conv_rhs => rw [Finset.sum_range_succ, add_pow]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [qBranch_one_row, qBinom_one_q, Nat.choose_symm hj, qWhittV_one_q_one_row a m j]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    ring

/-- **Principal specialisation of the one-row Schur polynomial**:
`h_n(1, q, …, q^m) = [m + n choose m]_q`. -/
theorem schurV_principal_one_row (q : R) : ∀ m n : ℕ,
    schurV (fun i => q ^ i) 1 (m + 1) (fun _ => n) = qBinom q (m + n) m
  | 0, n => by
    rw [schurV_succ, sum_interl_one, Finset.sum_eq_single 0]
    · rw [schurV_zero, if_pos (by funext i; rfl)]; simp
    · intro j _ hj
      rw [schurV_zero, if_neg (fun h => hj (by simpa using congrFun h 0))]; simp
    · simp
  | m + 1, n => by
    rw [schurV_succ, sum_interl_one, show m + 1 + n = m + 1 + n from rfl,
      qBinom_succ_right_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [schurV_principal_one_row q m j, ← pow_mul]
    simp

/-- **Euler's identity, finite form**: `(q; q)_n · [m + n choose m]_q = (q^{m+1}; q)_n`.
With `schurV_principal_one_row`, `(q; q)_n · h_n(1, q, …, q^m) = (q^{m+1}; q)_n`, which tends to `1`
as `m → ∞` for `|q| < 1`: `h_n(1, q, q², …) = 1 / (q; q)_n`, the `n`-th coefficient of the
one-variable q-Whittaker Cauchy kernel `1/(xy; q)_∞ = Σ_n P_{(n)}(x) Q_{(n)}(y)`. -/
theorem qPoch_mul_qBinom (q : R) : ∀ m n : ℕ,
    (∏ i ∈ range n, (1 - q ^ (i + 1))) * qBinom q (m + n) m = ∏ i ∈ range n, (1 - q ^ (m + 1 + i))
  | 0, n => by
    simp only [zero_add, qBinom_zero_right, mul_one]
    exact Finset.prod_congr rfl fun i _ => by ring_nf
  | m + 1, 0 => by simp
  | m + 1, n + 1 => by
    have h1 := qPoch_mul_qBinom q m (n + 1)
    have h2 := qPoch_mul_qBinom q (m + 1) n
    rw [show m + 1 + (n + 1) = (m + (n + 1)) + 1 by omega, qBinom_succ_succ,
      show m + (n + 1) = m + 1 + n by omega, Finset.prod_range_succ (fun i => 1 - q ^ (i + 1)),
      Finset.prod_range_succ (fun i => 1 - q ^ (m + 1 + 1 + i))]
    rw [show m + 1 + n = m + (n + 1) by omega] at h2 ⊢
    rw [Finset.prod_range_succ' (fun i => 1 - q ^ (m + 1 + i))] at h1
    have h3 : ∏ i ∈ range n, (1 - q ^ (m + 1 + (i + 1))) = ∏ i ∈ range n, (1 - q ^ (m + 1 + 1 + i)) :=
      Finset.prod_congr rfl fun i _ => by ring_nf
    rw [h3] at h1
    rw [show m + (n + 1) = m + 1 + n by omega] at h1 h2 ⊢
    rw [Finset.prod_range_succ (fun i => 1 - q ^ (i + 1))] at h1
    linear_combination h1 + q ^ (m + 1) * (1 - q ^ (n + 1)) * h2

/-! ### Real and complex kernels -/

/-- **Duplication of the q-Pochhammer kernel** (finite form): `(T; q)_{2M} = (T; q²)_M (qT; q²)_M`.
As `M → ∞`, the one-variable q-Whittaker Cauchy kernel `1/(T; q)_∞` at base `q` is the product of
two kernels at base `q²`, at `T` and `qT`: the q-shadow of `Γ_ℂ(s) = Γ_ℝ(s) Γ_ℝ(s + 1)`. -/
theorem prod_qPoch_duplication (q T : R) (M : ℕ) :
    ∏ i ∈ range (2 * M), (1 - q ^ i * T)
      = (∏ i ∈ range M, (1 - (q ^ 2) ^ i * T)) * ∏ i ∈ range M, (1 - (q ^ 2) ^ i * (q * T)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, Finset.prod_range_succ]
    rw [show q ^ (2 * M + 1) * T = q ^ (2 * M) * (q * T) by ring]
    ring

end RMT.Symmetric
