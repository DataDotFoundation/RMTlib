import RMTlib.Fock.Weil
import RMTlib.Fock.Laplacian
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The matrix-space pair `(U(k), U(p, q))`: joint harmonics from disjoint rows

Companion to `bridge/links/virasoro-briefing.md` (§12); checks in `bridge/scripts/matrix_pair.py`. GRH-free.

The Fock model `ℚ[M_{k×p}] ⊗ ℚ[M_{k×q}]` with coordinates `x_{li}` (`l < k`, `i < p`) and `y_{lj}` (`j < q`), the
second copy being the conjugate one. The lowering operators of the Weil `𝔲(p, q)` are the `U(k)`-invariant Laplacians

  `Δ_{ij} = Σ_{l<k} ∂/∂x_{li} ∂/∂y_{lj}`   (`lap`),

and the joint harmonics are their common kernel. This is Explorer's Step 1 for the archimedean Theta input
(the Fock side of Kashiwara–Vergne / Howe and Vogan, filed as `.scholzeInput .infty`).

## Main results

* `lap_mul_eq_zero`: **disjoint rows give harmonics**. If `f` involves only the `x`-rows `l < A` and `g` only the
  `y`-rows `l ≥ A`, then `Δ_{ij}(f g) = 0` for all `i, j`. Every term of `Σ_l ∂x_{li} f · ∂y_{lj} g` has one
  vanishing factor.
* `hvec_harmonic`: Kashiwara–Vergne's joint highest-weight vector
  `h_{λ⁺,λ⁻} = ∏_i D_i(x)^{λ⁺_i − λ⁺_{i+1}} · ∏_j D̃_j(y)^{λ⁻_j − λ⁻_{j+1}}`, with `D_i` the leading `i × i` minor of
  `x` and `D̃_j` the minor of `y` on the last `j` rows, is a joint harmonic whenever `ℓ(λ⁺) + ℓ(λ⁻) ≤ k`.
* `hvec_highest`: `h_{λ⁺,λ⁻}` is killed by every raising operator of `U(p)` (`colRaiseX`), `U(q)`
  (`colRaiseY`) and `U(k)` (`rowRaise`, which acts on `y` as on the conjugate copy). It is a joint highest-weight
  vector. Each raising operator replaces a row or column of a minor by its neighbour (`derivation_det`), giving
  a repeated line or a zero line.
* `hvec_isHomogeneous` (B, first half): `h_{λ⁺,λ⁻}` is homogeneous of degree `|λ⁺| + |λ⁻|`.
* `weight_imp_degree` (B, second half): a nonzero homogeneous weight vector of weight `(λ⁺, λ⁻)` has degree
  `|λ⁺| + |λ⁻|`, so no vector of that weight lives in another degree.
* `lap_E`: the `k/2` shift: `[Δ_{ij}, E_{ij}] = k + Σ_l x_{li}∂x_{li} + Σ_l y_{lj}∂y_{lj}`, with
  `E_{ij} = Σ_l x_{li} y_{lj}`. It is the unitary pair of `RMTlib.Fock.Weil` with `m = k`, so the twist is
  `det^{k/2}` per side.

Computed only (`matrix_pair.py`): these are all the joint highest-weight vectors, one per `(λ⁺, λ⁻)` (multiplicity
one, Step 2), with `U(k)`-weight `(λ⁺, 0, …, 0, −rev λ⁻)`, and minimal degree = minimal K-type. Not stated here: the
weights of `h_{λ⁺,λ⁻}` themselves (its Euler eigenvalues).
-/

open MvPolynomial Finset

namespace RMT.Fock.MatrixPair

variable (k p q : ℕ)

/-- The variables: `inl (l, i) = x_{li}`, `inr (l, j) = y_{lj}`. -/
abbrev V := (Fin k × Fin p) ⊕ (Fin k × Fin q)

/-- The Fock model `ℚ[M_{k×p}] ⊗ ℚ[M_{k×q}]`. -/
abbrev P := MvPolynomial (V k p q) ℚ

variable {k p q}

/-- `Δ_{ij} = Σ_l ∂x_{li} ∂y_{lj}`. -/
noncomputable def lap (i : Fin p) (j : Fin q) (f : P k p q) : P k p q :=
  ∑ l : Fin k, pderiv (Sum.inl (l, i)) (pderiv (Sum.inr (l, j)) f)

/-- The `x`-variables in rows `< A`. -/
def xRows (A : ℕ) : Set (V k p q) := {v | ∃ l i, v = Sum.inl (l, i) ∧ (l : ℕ) < A}

/-- The `y`-variables in rows `≥ A`. -/
def yRows (A : ℕ) : Set (V k p q) := {v | ∃ l j, v = Sum.inr (l, j) ∧ A ≤ (l : ℕ)}

theorem pderiv_eq_zero_of_supported {S : Set (V k p q)} {f : P k p q} (hf : f ∈ supported ℚ S)
    {v : V k p q} (hv : v ∉ S) : pderiv v f = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  exact hv ((mem_supported.mp hf) h)

/-- **Disjoint rows give joint harmonics**: `Δ_{ij}(f g) = 0` when `f` lives on the `x`-rows `< A` and `g` on
the `y`-rows `≥ A`. -/
theorem lap_mul_eq_zero (A : ℕ) {f g : P k p q} (hf : f ∈ supported ℚ (xRows A))
    (hg : g ∈ supported ℚ (yRows A)) (i : Fin p) (j : Fin q) : lap i j (f * g) = 0 := by
  unfold lap
  refine Finset.sum_eq_zero fun l _ => ?_
  have hfy : pderiv (Sum.inr (l, j)) f = 0 :=
    pderiv_eq_zero_of_supported hf (by rintro ⟨_, _, h, _⟩; cases h)
  have hgx : pderiv (Sum.inl (l, i)) g = 0 :=
    pderiv_eq_zero_of_supported hg (by rintro ⟨_, _, h, _⟩; cases h)
  have hcomm : pderiv (Sum.inl (l, i)) (pderiv (Sum.inr (l, j)) g) = 0 := by
    have := congrArg (· g) (RMT.Fock.Weil.D_D_comm (σ := V k p q) (Sum.inl (l, i)) (Sum.inr (l, j)))
    simp only [RMT.Fock.Weil.D, Module.End.mul_apply, Derivation.coeFn_coe] at this
    rw [this, hgx, map_zero]
  rw [Derivation.leibniz, hfy, smul_zero, add_zero, smul_eq_mul, Derivation.leibniz, hcomm, smul_zero,
    zero_add, smul_eq_mul]
  by_cases hl : (l : ℕ) < A
  · rw [pderiv_eq_zero_of_supported hg (by rintro ⟨l', j', h, h'⟩; cases h; omega), zero_mul]
  · rw [pderiv_eq_zero_of_supported hf (by rintro ⟨l', i', h, h'⟩; cases h; omega), mul_zero]

/-! ## The minors and Kashiwara–Vergne's vector -/

/-- The leading `r × r` minor of `x` (`1` if `r > k` or `r > p`). -/
noncomputable def xMinor (r : ℕ) : P k p q :=
  if h : r ≤ k ∧ r ≤ p then
    (Matrix.of fun a b : Fin r => (X (Sum.inl (Fin.castLE h.1 a, Fin.castLE h.2 b)) : P k p q)).det
  else 1

/-- The minor of `y` on its last `r` rows and first `r` columns (`1` if `r > k` or `r > q`). -/
noncomputable def yMinor (r : ℕ) : P k p q :=
  if h : r ≤ k ∧ r ≤ q then
    (Matrix.of fun a b : Fin r =>
      (X (Sum.inr ((⟨k - r + a, by omega⟩ : Fin k), Fin.castLE h.2 b)) : P k p q)).det
  else 1

theorem det_mem_supported {r : ℕ} {S : Set (V k p q)} (M : Matrix (Fin r) (Fin r) (P k p q))
    (hM : ∀ a b, M a b ∈ supported ℚ S) : M.det ∈ supported ℚ S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun a _ => hM _ _) _

theorem xMinor_mem (A r : ℕ) (hr : r ≤ A) : (xMinor r : P k p q) ∈ supported ℚ (xRows A) := by
  unfold xMinor
  split_ifs with h
  · refine det_mem_supported _ fun a b => ?_
    exact (mem_supported.mpr (by
      simp only [Matrix.of_apply, vars_X, Finset.coe_singleton, Set.singleton_subset_iff]
      exact ⟨_, _, rfl, by simp; omega⟩))
  · exact Subalgebra.one_mem _

theorem yMinor_mem (B r : ℕ) (hr : r ≤ B) :
    (yMinor r : P k p q) ∈ supported ℚ (yRows (k - B)) := by
  unfold yMinor
  split_ifs with h
  · refine det_mem_supported _ fun a b => ?_
    exact (mem_supported.mpr (by
      simp only [Matrix.of_apply, vars_X, Finset.coe_singleton, Set.singleton_subset_iff]
      exact ⟨_, _, rfl, by simp; omega⟩))
  · exact Subalgebra.one_mem _

/-- **Kashiwara–Vergne's joint highest-weight vector** `h_{λ⁺,λ⁻}`, for `λ⁺` of length `≤ A` and `λ⁻` of
length `≤ B` (as sequences `ℕ → ℕ`). -/
noncomputable def hvec (lp lm : ℕ → ℕ) (A B : ℕ) : P k p q :=
  (∏ i ∈ range A, xMinor (i + 1) ^ (lp i - lp (i + 1))) *
    ∏ j ∈ range B, yMinor (j + 1) ^ (lm j - lm (j + 1))

/-- **`h_{λ⁺,λ⁻}` is a joint harmonic** when `ℓ(λ⁺) + ℓ(λ⁻) ≤ k`: `Δ_{ij} h = 0` for all `i, j`. -/
theorem hvec_harmonic (lp lm : ℕ → ℕ) (A B : ℕ) (hAB : A + B ≤ k) (i : Fin p) (j : Fin q) :
    lap i j (hvec lp lm A B : P k p q) = 0 := by
  refine lap_mul_eq_zero A ?_ ?_ i j
  · exact Subalgebra.prod_mem _ fun r hr =>
      Subalgebra.pow_mem _ (xMinor_mem A (r + 1) (by simp at hr; omega)) _
  · have hsub : ∀ g : P k p q, g ∈ supported ℚ (yRows (k - B)) → g ∈ supported ℚ (yRows A) := by
      intro g hg
      exact supported_mono (by rintro v ⟨l, j, rfl, hl⟩; exact ⟨l, j, rfl, by omega⟩) hg
    exact hsub _ (Subalgebra.prod_mem _ fun r hr =>
      Subalgebra.pow_mem _ (yMinor_mem B (r + 1) (by simp at hr; omega)) _)

/-! ## Degree: `h_{λ⁺,λ⁻}` is homogeneous of degree `|λ⁺| + |λ⁻|` -/

theorem det_isHomogeneous {r : ℕ} (M : Matrix (Fin r) (Fin r) (P k p q))
    (hM : ∀ a b, (M a b).IsHomogeneous 1) : M.det.IsHomogeneous r := by
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hprod : (∏ a, M (σ a) a).IsHomogeneous r := by
    have := IsHomogeneous.prod Finset.univ (fun a => M (σ a) a) (fun _ => 1) (fun a _ => hM _ _)
    simpa using this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hprod
  · rw [h, Units.neg_smul, one_smul]; exact hprod.neg

theorem xMinor_isHomogeneous (r : ℕ) (h : r ≤ k ∧ r ≤ p) : (xMinor r : P k p q).IsHomogeneous r := by
  rw [xMinor, dite_eq_left h]
  exact det_isHomogeneous _ fun _ _ => isHomogeneous_X _ _

theorem yMinor_isHomogeneous (r : ℕ) (h : r ≤ k ∧ r ≤ q) : (yMinor r : P k p q).IsHomogeneous r := by
  rw [yMinor, dite_eq_left h]
  exact det_isHomogeneous _ fun _ _ => isHomogeneous_X _ _

theorem sum_telescope (l : ℕ → ℕ) (hl : Antitone l) (A : ℕ) :
    (∑ i ∈ range A, (i + 1) * (l i - l (i + 1)) : ℕ) + A * l A = ∑ i ∈ range A, l i := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    have h1 : l (A + 1) ≤ l A := hl (Nat.le_succ A)
    zify [h1]
    ring

/-- **(B) Degree**: for `λ⁺` of length `≤ A ≤ min(k, p)` and `λ⁻` of length `≤ B ≤ min(k, q)`, the vector
`h_{λ⁺,λ⁻}` is homogeneous of degree `|λ⁺| + |λ⁻|`. -/
theorem hvec_isHomogeneous (lp lm : ℕ → ℕ) (hp : Antitone lp) (hm : Antitone lm) (A B : ℕ)
    (hA : A ≤ k ∧ A ≤ p) (hB : B ≤ k ∧ B ≤ q) (hpA : lp A = 0) (hmB : lm B = 0) :
    (hvec lp lm A B : P k p q).IsHomogeneous ((∑ i ∈ range A, lp i) + ∑ j ∈ range B, lm j) := by
  have tA := sum_telescope lp hp A
  have tB := sum_telescope lm hm B
  rw [hpA, mul_zero, add_zero] at tA
  rw [hmB, mul_zero, add_zero] at tB
  rw [← tA, ← tB, hvec]
  refine IsHomogeneous.mul ?_ ?_
  · refine IsHomogeneous.prod _ _ _ fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have := (xMinor_isHomogeneous (k := k) (p := p) (q := q) (i + 1) ⟨by omega, by omega⟩).pow
      (lp i - lp (i + 1))
    convert this using 1
  · refine IsHomogeneous.prod _ _ _ fun j hj => ?_
    simp only [Finset.mem_range] at hj
    have := (yMinor_isHomogeneous (k := k) (p := p) (q := q) (j + 1) ⟨by omega, by omega⟩).pow
      (lm j - lm (j + 1))
    convert this using 1

/-! ## The `k/2` shift: `[Δ_{ij}, E_{ij}] = k + Eul^x_i + Eul^y_j` -/

/-- `E_{ij} = Σ_l x_{li} y_{lj}`. -/
noncomputable def E (i : Fin p) (j : Fin q) : P k p q := ∑ l : Fin k, X (Sum.inl (l, i)) * X (Sum.inr (l, j))

theorem lap_E (i : Fin p) (j : Fin q) (f : P k p q) :
    lap i j (E i j * f) - E i j * lap i j f =
      (k : ℚ) • f + ∑ l : Fin k, X (Sum.inl (l, i)) * pderiv (Sum.inl (l, i)) f +
        ∑ l : Fin k, X (Sum.inr (l, j)) * pderiv (Sum.inr (l, j)) f := by
  classical
  simp only [lap, E, Finset.sum_mul, Finset.mul_sum, map_sum, Derivation.leibniz, smul_eq_mul, pderiv_X,
    Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq, and_true, ite_false,
    map_add, mul_zero, add_zero, zero_add, mul_ite, mul_one]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h3 : ∀ x : Fin k, (∑ x_1 : Fin k, pderiv (Sum.inl (x, i))
      (if x_1 = x then f * X (Sum.inl (x_1, i)) else 0)) = f + X (Sum.inl (x, i)) * pderiv (Sum.inl (x, i)) f := by
    intro x
    rw [Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
    simp [Derivation.leibniz, pderiv_X]
  simp only [h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℚ]
  simp only [mul_comm (pderiv (Sum.inr _) f)]
  abel

/-! ## Highest weight: the raising operators kill `h_{λ⁺,λ⁻}` -/

/-- A derivation kills a determinant if each row-updated determinant vanishes. -/
theorem der_det_eq_zero {r : ℕ} (D : Derivation ℚ (P k p q) (P k p q)) (M : Matrix (Fin r) (Fin r) (P k p q))
    (h : ∀ a, (M.updateRow a fun b => D (M a b)).det = 0) : D M.det = 0 := by
  rw [RMT.Fock.derivation_det]; exact Finset.sum_eq_zero fun a _ => h a

/-- The same, column by column (rows of the transpose). -/
theorem der_det_eq_zero' {r : ℕ} (D : Derivation ℚ (P k p q) (P k p q)) (M : Matrix (Fin r) (Fin r) (P k p q))
    (h : ∀ b, (M.transpose.updateRow b fun a => D (M a b)).det = 0) : D M.det = 0 := by
  rw [← Matrix.det_transpose]
  exact der_det_eq_zero D _ h

/-- A determinant vanishes if an updated row is `c` times another row. -/
theorem det_updateRow_smul_row {r : ℕ} (M : Matrix (Fin r) (Fin r) (P k p q)) {a a' : Fin r} (h : a ≠ a')
    (c : P k p q) : (M.updateRow a fun b => c * M a' b).det = 0 := by
  have : (fun b => c * M a' b) = c • M a' := by ext b; simp
  rw [this, Matrix.det_updateRow_smul, Matrix.det_zero_of_row_eq h (by
    rw [Matrix.updateRow_self, Matrix.updateRow_ne (Ne.symm h)]), mul_zero]

/-- A derivation killing every factor kills a product of powers. -/
theorem der_prod_pow_eq_zero {ι : Type*} (D : Derivation ℚ (P k p q) (P k p q)) (s : Finset ι)
    (f : ι → P k p q) (e : ι → ℕ) (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i ^ e i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, Derivation.leibniz_pow, h a (Finset.mem_insert_self _ _),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]
    simp

theorem kill_zero {r : ℕ} (D : Derivation ℚ (P k p q) (P k p q)) (M : Matrix (Fin r) (Fin r) (P k p q))
    (h : ∀ a b, D (M a b) = 0) : D M.det = 0 :=
  der_det_eq_zero D M fun a => Matrix.det_eq_zero_of_row_eq_zero a fun b => by simp [h]

theorem kill_row {r : ℕ} (D : Derivation ℚ (P k p q) (P k p q)) (M : Matrix (Fin r) (Fin r) (P k p q))
    {a0 a1 : Fin r} (hne : a0 ≠ a1) (c : P k p q)
    (h : ∀ a b, D (M a b) = if a = a0 then c * M a1 b else 0) : D M.det = 0 := by
  refine der_det_eq_zero D M fun a => ?_
  by_cases ha : a = a0
  · subst ha; simp only [h, ite_true]; exact det_updateRow_smul_row M hne c
  · exact Matrix.det_eq_zero_of_row_eq_zero a fun b => by simp [h, ha]

theorem kill_col {r : ℕ} (D : Derivation ℚ (P k p q) (P k p q)) (M : Matrix (Fin r) (Fin r) (P k p q))
    {b0 b1 : Fin r} (hne : b0 ≠ b1) (h : ∀ a b, D (M a b) = if b = b0 then M a b1 else 0) :
    D M.det = 0 := by
  refine der_det_eq_zero' D M fun b => ?_
  by_cases hb : b = b0
  · subst hb
    have := det_updateRow_smul_row M.transpose hne 1
    simpa [h, Matrix.transpose_apply] using this
  · exact Matrix.det_eq_zero_of_row_eq_zero b fun a => by simp [h, hb]

/-- The `U(p)` raising operator `Σ_l x_{lc} ∂/∂x_{lc'}` (`c' = c + 1`), given on the variables. -/
noncomputable def colRaiseX (c c' : Fin p) : Derivation ℚ (P k p q) (P k p q) :=
  mkDerivation ℚ (Sum.elim (fun v => if v.2 = c' then X (Sum.inl (v.1, c)) else 0) fun _ => 0)

/-- The `U(q)` raising operator `Σ_l y_{lc} ∂/∂y_{lc'}` (`c' = c + 1`). -/
noncomputable def colRaiseY (c c' : Fin q) : Derivation ℚ (P k p q) (P k p q) :=
  mkDerivation ℚ (Sum.elim (fun _ => 0) fun v => if v.2 = c' then X (Sum.inr (v.1, c)) else 0)

/-- The `U(k)` raising operator `Σ_j x_{aj} ∂/∂x_{a'j} − Σ_j y_{a'j} ∂/∂y_{aj}` (`a' = a + 1`; `y` is the
conjugate copy). -/
noncomputable def rowRaise (a a' : Fin k) : Derivation ℚ (P k p q) (P k p q) :=
  mkDerivation ℚ (Sum.elim (fun v => if v.1 = a' then X (Sum.inl (a, v.2)) else 0)
    fun v => if v.1 = a then -X (Sum.inr (a', v.2)) else 0)

theorem colRaiseX_inl (c c' : Fin p) (l : Fin k) (b : Fin p) :
    colRaiseX c c' (X (Sum.inl (l, b)) : P k p q) = if b = c' then X (Sum.inl (l, c)) else 0 :=
  mkDerivation_X _ _ _

theorem colRaiseX_inr (c c' : Fin p) (l : Fin k) (b : Fin q) :
    colRaiseX c c' (X (Sum.inr (l, b)) : P k p q) = 0 := mkDerivation_X _ _ _

theorem colRaiseY_inr (c c' : Fin q) (l : Fin k) (b : Fin q) :
    colRaiseY c c' (X (Sum.inr (l, b)) : P k p q) = if b = c' then X (Sum.inr (l, c)) else 0 :=
  mkDerivation_X _ _ _

theorem colRaiseY_inl (c c' : Fin q) (l : Fin k) (b : Fin p) :
    colRaiseY c c' (X (Sum.inl (l, b)) : P k p q) = 0 := mkDerivation_X _ _ _

theorem rowRaise_inl (a a' : Fin k) (l : Fin k) (b : Fin p) :
    rowRaise a a' (X (Sum.inl (l, b)) : P k p q) = if l = a' then X (Sum.inl (a, b)) else 0 :=
  mkDerivation_X _ _ _

theorem rowRaise_inr (a a' : Fin k) (l : Fin k) (b : Fin q) :
    rowRaise a a' (X (Sum.inr (l, b)) : P k p q) = if l = a then -X (Sum.inr (a', b)) else 0 :=
  mkDerivation_X _ _ _

/-! ### Each raising operator kills each minor -/

theorem colRaiseX_xMinor (c c' : Fin p) (hc : (c' : ℕ) = c + 1) (r : ℕ) :
    colRaiseX c c' (xMinor r : P k p q) = 0 := by
  unfold xMinor
  split_ifs with h
  · by_cases hr : (c' : ℕ) < r
    · refine kill_col _ _ (b0 := ⟨c', hr⟩) (b1 := ⟨c, by omega⟩) (by simp [Fin.ext_iff]; omega) fun a b => ?_
      simp only [Matrix.of_apply, colRaiseX_inl, Fin.ext_iff, Fin.val_castLE]
      split_ifs <;> rfl
    · exact kill_zero _ _ fun a b => by
        simp only [Matrix.of_apply, colRaiseX_inl, Fin.ext_iff, Fin.val_castLE]
        rw [ite_eq_right (by omega)]
  · simp

theorem colRaiseY_xMinor (c c' : Fin q) (r : ℕ) : colRaiseY c c' (xMinor r : P k p q) = 0 := by
  unfold xMinor
  split_ifs
  · exact kill_zero _ _ fun a b => by simp [colRaiseY_inl]
  · simp

theorem rowRaise_xMinor (a a' : Fin k) (ha : (a' : ℕ) = a + 1) (r : ℕ) :
    rowRaise a a' (xMinor r : P k p q) = 0 := by
  unfold xMinor
  split_ifs with h
  · by_cases hr : (a' : ℕ) < r
    · refine kill_row _ _ (a0 := ⟨a', hr⟩) (a1 := ⟨a, by omega⟩) (by simp [Fin.ext_iff]; omega) 1
        fun i b => ?_
      simp only [Matrix.of_apply, rowRaise_inl, Fin.ext_iff, Fin.val_castLE, one_mul]
      split_ifs <;> rfl
    · exact kill_zero _ _ fun i b => by
        simp only [Matrix.of_apply, rowRaise_inl, Fin.ext_iff, Fin.val_castLE]
        rw [ite_eq_right (by omega)]
  · simp

theorem colRaiseX_yMinor (c c' : Fin p) (r : ℕ) : colRaiseX c c' (yMinor r : P k p q) = 0 := by
  unfold yMinor
  split_ifs
  · exact kill_zero _ _ fun a b => by simp [colRaiseX_inr]
  · simp

theorem colRaiseY_yMinor (c c' : Fin q) (hc : (c' : ℕ) = c + 1) (r : ℕ) :
    colRaiseY c c' (yMinor r : P k p q) = 0 := by
  unfold yMinor
  split_ifs with h
  · by_cases hr : (c' : ℕ) < r
    · refine kill_col _ _ (b0 := ⟨c', hr⟩) (b1 := ⟨c, by omega⟩) (by simp [Fin.ext_iff]; omega) fun a b => ?_
      simp only [Matrix.of_apply, colRaiseY_inr, Fin.ext_iff, Fin.val_castLE]
      split_ifs <;> rfl
    · exact kill_zero _ _ fun a b => by
        simp only [Matrix.of_apply, colRaiseY_inr, Fin.ext_iff, Fin.val_castLE]
        rw [ite_eq_right (by omega)]
  · simp

theorem rowRaise_yMinor (a a' : Fin k) (ha : (a' : ℕ) = a + 1) (r : ℕ) :
    rowRaise a a' (yMinor r : P k p q) = 0 := by
  unfold yMinor
  split_ifs with h
  · by_cases hr : k - r ≤ (a : ℕ)
    · refine kill_row _ _ (a0 := ⟨a - (k - r), by omega⟩) (a1 := ⟨a - (k - r) + 1, by omega⟩)
        (by simp [Fin.ext_iff]) (-1) fun i b => ?_
      simp only [Matrix.of_apply, rowRaise_inr, Fin.ext_iff]
      split_ifs <;> try (exfalso; omega)
      · rw [neg_one_mul]; congr 3; refine Prod.ext ?_ rfl; ext; simp; omega
      · rfl
    · exact kill_zero _ _ fun i b => by
        simp only [Matrix.of_apply, rowRaise_inr, Fin.ext_iff]
        rw [ite_eq_right (by omega)]
  · simp

theorem der_hvec (D : Derivation ℚ (P k p q) (P k p q)) (hx : ∀ r, D (xMinor r : P k p q) = 0)
    (hy : ∀ r, D (yMinor r : P k p q) = 0) (lp lm : ℕ → ℕ) (A B : ℕ) : D (hvec lp lm A B : P k p q) = 0 := by
  rw [hvec, Derivation.leibniz, der_prod_pow_eq_zero _ _ _ _ (fun i _ => hx _),
    der_prod_pow_eq_zero _ _ _ _ (fun i _ => hy _)]
  simp

/-- **(A) `h_{λ⁺,λ⁻}` is a highest-weight vector**: every raising operator of `U(p)`, `U(q)` and `U(k)` kills it. -/
theorem hvec_highest (lp lm : ℕ → ℕ) (A B : ℕ) :
    (∀ c c' : Fin p, (c' : ℕ) = c + 1 → colRaiseX c c' (hvec lp lm A B : P k p q) = 0) ∧
    (∀ c c' : Fin q, (c' : ℕ) = c + 1 → colRaiseY c c' (hvec lp lm A B : P k p q) = 0) ∧
    (∀ a a' : Fin k, (a' : ℕ) = a + 1 → rowRaise a a' (hvec lp lm A B : P k p q) = 0) :=
  ⟨fun c c' hc => der_hvec _ (colRaiseX_xMinor c c' hc) (colRaiseX_yMinor c c') _ _ _ _,
   fun c c' hc => der_hvec _ (colRaiseY_xMinor c c') (colRaiseY_yMinor c c' hc) _ _ _ _,
   fun a a' ha => der_hvec _ (rowRaise_xMinor a a' ha) (rowRaise_yMinor a a' ha) _ _ _ _⟩

/-! ## (B) A weight vector of weight `(λ⁺, λ⁻)` has degree `|λ⁺| + |λ⁻|` -/

/-- **Weight counting** (B, the "minimal degree" half): a nonzero homogeneous `f` of degree `n` that is a
`U(p) × U(q)` weight vector, `Σ_l x_{li}∂x_{li} f = λ⁺_i f` and `Σ_l y_{lj}∂y_{lj} f = λ⁻_j f`, has
`n = Σ λ⁺ + Σ λ⁻`. The column Euler operators sum to the degree operator. -/
theorem weight_imp_degree (f : P k p q) (n : ℕ) (hf : f.IsHomogeneous n) (hf0 : f ≠ 0)
    (lp : Fin p → ℚ) (lm : Fin q → ℚ)
    (hx : ∀ i, ∑ l : Fin k, X (Sum.inl (l, i)) * pderiv (Sum.inl (l, i)) f = lp i • f)
    (hy : ∀ j, ∑ l : Fin k, X (Sum.inr (l, j)) * pderiv (Sum.inr (l, j)) f = lm j • f) :
    (n : ℚ) = ∑ i, lp i + ∑ j, lm j := by
  have he := hf.sum_X_mul_pderiv
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_comm (f := fun (l : Fin k) (j : Fin q) => X (Sum.inr (l, j)) * pderiv (Sum.inr (l, j)) f)] at he
  simp only [hx, hy, ← Finset.sum_smul] at he
  rw [← add_smul, ← Nat.cast_smul_eq_nsmul ℚ] at he
  have h0 : ((∑ i, lp i + ∑ j, lm j) - n) • f = 0 := by rw [sub_smul, he, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · linarith
  · exact absurd h hf0

end RMT.Fock.MatrixPair
