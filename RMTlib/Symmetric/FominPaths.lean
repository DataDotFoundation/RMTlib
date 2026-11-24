import RMTlib.Symmetric.CornerWeighted

/-!
# Path counting: from `[D, U] = h(level)` to `D^n U^n e_∅`

**The general lemma** (any module, any graded pair of operators). Let `D, U` be endomorphisms of an
`R`-module and `v` a vector with `D v = 0`. If the commutator acts on the `m`-th level by a scalar,
`[D, U] (U^m v) = h(m) U^m v`, then

  `D (U^{n+1} v) = (Σ_{m ≤ n} h(m)) U^n v`,   `D^n U^n v = ∏_{j < n} (Σ_{m ≤ j} h(m)) · v`

(`down_up_pow_succ`, `down_pow_up_pow`). `D^n U^n v` is the total weight of the paths that go up
`n` steps and back down: Fomin's path identity, for any differential-type graded graph.

**On Young's lattice** (`e_∅ = single 0 1`), `U^m e_∅` is supported on the partitions of size `m`
(`upW_pow_vacuum_mem`), and a partition of size `< N` is not full, so the commutator formulas of
`RMT.Symmetric.Corners` apply level by level when `n ≤ N`:

* **Fomin** (`r u` affine): `D_r^n U_u^n e_∅ = n! (r u)(0)^n e_∅` (`fomin_paths`).
* **sl₂** (`r = a c + b`, `u = a' c + b'`): `D_r^n U_u^n e_∅ = n! ∏_{j<n} (b b' + a a' j) e_∅`
  (`sl2_paths`). With `r = z' + c`, `u = z + c` this is `n! (zz')_n`, the z-measure normalisation
  (`zmeasure_paths`); with `u = z − c` (fermionic twin) it is `n! zz'(zz'−1)⋯(zz'−n+1)`
  (`zmeasure_paths_twin`).
-/

open Finset

noncomputable section

/-! ## The general lemma -/

section General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **One step down**: if `D v = 0` and `[D, U] = h(m)` on the `m`-th level for `m ≤ n`, then
`D (U^{n+1} v) = (Σ_{m ≤ n} h(m)) U^n v`. -/
theorem down_up_pow_succ (D U : Module.End R M) (v : M) (hv : D v = 0) (h : ℕ → R) (n : ℕ)
    (hc : ∀ m ≤ n, D (U ((U ^ m) v)) - U (D ((U ^ m) v)) = h m • (U ^ m) v) :
    D ((U ^ (n + 1)) v) = (∑ m ∈ range (n + 1), h m) • (U ^ n) v := by
  induction n with
  | zero =>
    have := hc 0 le_rfl
    simp only [pow_zero, Module.End.one_apply, hv, map_zero, sub_zero] at this
    simp [pow_one, this]
  | succ n ih =>
    have h1 := hc (n + 1) le_rfl
    rw [pow_succ', Module.End.mul_apply, sub_eq_iff_eq_add.mp h1,
      ih fun m hm => hc m (by omega), map_smul, ← Module.End.mul_apply, ← pow_succ']
    simp only [sum_range_succ, add_smul]
    abel

/-- **Fomin's path identity, abstractly**: `D^n U^n v = ∏_{j<n} (Σ_{m ≤ j} h(m)) · v`. -/
theorem down_pow_up_pow (D U : Module.End R M) (v : M) (hv : D v = 0) (h : ℕ → R) (n : ℕ)
    (hc : ∀ m < n, D (U ((U ^ m) v)) - U (D ((U ^ m) v)) = h m • (U ^ m) v) :
    (D ^ n) ((U ^ n) v) = (∏ j ∈ range n, ∑ m ∈ range (j + 1), h m) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply,
      down_up_pow_succ D U v hv h n fun m hm => hc m (by omega), map_smul,
      ih fun m hm => hc m (by omega), smul_smul, prod_range_succ, mul_comm]

/-- With a constant commutator `h(m) = c` (Fomin's form): `D^n U^n v = n! c^n v`. -/
theorem down_pow_up_pow_const (D U : Module.End R M) (v : M) (hv : D v = 0) (c : R) (n : ℕ)
    (hc : ∀ m < n, D (U ((U ^ m) v)) - U (D ((U ^ m) v)) = c • (U ^ m) v) :
    (D ^ n) ((U ^ n) v) = ((n.factorial : R) * c ^ n) • v := by
  rw [down_pow_up_pow D U v hv (fun _ => c) n hc]
  congr 1
  clear hc
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, Nat.factorial_succ]
    simp only [sum_const, card_range, nsmul_eq_mul]
    push_cast; ring

/-- With `h(m) = β + 2 α m` (sl₂): `D^n U^n v = n! ∏_{j<n} (β + α j) · v`. -/
theorem down_pow_up_pow_sl2 (D U : Module.End R M) (v : M) (hv : D v = 0) (α β : R) (n : ℕ)
    (hc : ∀ m < n, D (U ((U ^ m) v)) - U (D ((U ^ m) v)) = (β + 2 * α * m) • (U ^ m) v) :
    (D ^ n) ((U ^ n) v) = ((n.factorial : R) * ∏ j ∈ range n, (β + α * j)) • v := by
  rw [down_pow_up_pow D U v hv (fun m => β + 2 * α * m) n hc]
  congr 1
  have hs : ∀ j : ℕ, ∑ m ∈ range (j + 1), (β + 2 * α * (m : R)) = (j + 1 : R) * (β + α * j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [sum_range_succ, ih]; push_cast; ring
  simp_rw [hs]
  rw [prod_mul_distrib]
  congr 1
  rw [← prod_range_add_one_eq_factorial]
  push_cast
  rfl

end General

/-! ## On Young's lattice -/

namespace RMT.Symmetric.Corners

variable {N : ℕ} {R : Type*} [CommRing R]

/-- The partitions of size `m` on `N` rows. -/
def level (N m : ℕ) : Set (Fin N → ℕ) := {ν | Antitone ν ∧ ∑ i, ν i = m}

/-- The vacuum `e_∅`. -/
def vacuum (N : ℕ) (R : Type*) [CommRing R] : (Fin N → ℕ) →₀ R := Finsupp.single 0 1

/-- **`D_r e_∅ = 0`**: the empty shape has no removable box. -/
theorem down_vacuum (r : ℤ → R) : down N r (vacuum N R) = 0 := by
  rw [vacuum, down_single, one_smul, downVec]
  refine sum_eq_zero fun i _ => ?_
  simp [RMT.IsCorner]

theorem vacuum_mem_level : vacuum N R ∈ Finsupp.supported R R (level N 0) :=
  Finsupp.single_mem_supported R _ ⟨fun _ _ _ => le_rfl, by simp⟩

/-- **`U_u` raises the level by one.** -/
theorem upW_mem_level (u : ℤ → R) {m : ℕ} {f : (Fin N → ℕ) →₀ R}
    (hf : f ∈ Finsupp.supported R R (level N m)) :
    upW N u f ∈ Finsupp.supported R R (level N (m + 1)) := by
  rw [upW, Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun ν hν => Submodule.smul_mem _ _ ?_
  obtain ⟨hanti, hsum⟩ := (Finsupp.mem_supported R f).1 hf hν
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with ha
  · exact Finsupp.single_mem_supported R _
      ⟨RMT.addBox_antitone hanti ha, by rw [RMT.sum_addBox, hsum]⟩
  · exact Submodule.zero_mem _

/-- `U_u^m e_∅` lives on the partitions of size `m`. -/
theorem upW_pow_vacuum_mem (u : ℤ → R) (m : ℕ) :
    (upW N u ^ m) (vacuum N R) ∈ Finsupp.supported R R (level N m) := by
  induction m with
  | zero => simpa using vacuum_mem_level
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact upW_mem_level u ih

/-- A linear map acting by `c` on every basis vector of a set acts by `c` on everything supported
there. -/
theorem apply_eq_smul_of_supported (C : ((Fin N → ℕ) →₀ R) →ₗ[R] ((Fin N → ℕ) →₀ R))
    (s : Set (Fin N → ℕ)) (c : R) (hC : ∀ ν ∈ s, C (Finsupp.single ν 1) = c • Finsupp.single ν 1)
    {f : (Fin N → ℕ) →₀ R} (hf : f ∈ Finsupp.supported R R s) : C f = c • f := by
  have key : ∀ ν ∈ f.support, C (Finsupp.single ν (f ν)) = c • Finsupp.single ν (f ν) := by
    intro ν hν
    rw [← Finsupp.smul_single_one, map_smul, hC ν ((Finsupp.mem_supported R f).1 hf hν),
      smul_comm]
  conv_lhs => rw [← f.sum_single]
  rw [map_finsuppSum, Finsupp.sum, sum_congr rfl key, ← smul_sum]
  conv_rhs => rw [← f.sum_single]
  rfl

/-- A partition of size `< N` on `N` rows is not full. -/
theorem not_full_of_sum_lt {ν : Fin N → ℕ} (h : ∑ i, ν i < N) : ¬ Full ν := by
  intro hfull
  have : ∑ _i : Fin N, 1 ≤ ∑ i, ν i := sum_le_sum fun i _ => hfull i
  simp at this
  omega

/-- **The level-wise commutator on Young's lattice**: if `[D_r, U_u] e_ν = h(|ν|) e_ν` on every
partition of size `< N`, then the hypothesis of the general lemma holds for `n ≤ N`. -/
theorem comm_level (r u : ℤ → R) (h : ℕ → R)
    (hν : ∀ ν : Fin N → ℕ, Antitone ν → ∑ i, ν i < N →
      down N r (upW N u (Finsupp.single ν 1)) - upW N u (down N r (Finsupp.single ν 1)) =
        h (∑ i, ν i) • Finsupp.single ν 1)
    {n : ℕ} (hn : n ≤ N) :
    ∀ m < n, down N r (upW N u ((upW N u ^ m) (vacuum N R))) -
        upW N u (down N r ((upW N u ^ m) (vacuum N R))) =
      h m • (upW N u ^ m) (vacuum N R) := by
  intro m hm
  have := apply_eq_smul_of_supported (down N r ∘ₗ upW N u - upW N u ∘ₗ down N r) (level N m)
    (h m) (fun ν ⟨hanti, hsum⟩ => by
      simpa [hsum] using hν ν hanti (by omega)) (upW_pow_vacuum_mem u m)
  simpa using this

/-- **Fomin's path identity on Young's lattice**: if `r u` is affine, then for `n ≤ N`,
`D_r^n U_u^n e_∅ = n! (r u)(0)^n e_∅`. -/
theorem fomin_paths {r u : ℤ → R} (hru : IsAffine (fun c => r c * u c)) {n : ℕ} (hn : n ≤ N) :
    (down N r ^ n) ((upW N u ^ n) (vacuum N R)) =
      ((n.factorial : R) * (r 0 * u 0) ^ n) • vacuum N R :=
  down_pow_up_pow_const _ _ _ (down_vacuum r) _ n
    (comm_level r u (fun _ => r 0 * u 0) (fun _ν hanti hlt =>
      commutator_weighted_of_not_full hanti (not_full_of_sum_lt hlt) hru) hn)

/-- **The sl₂ path identity**: for `r = a c + b`, `u = a' c + b'` and `n ≤ N`,
`D_r^n U_u^n e_∅ = n! ∏_{j<n} (b b' + a a' j) e_∅`. -/
theorem sl2_paths (a b a' b' : R) {n : ℕ} (hn : n ≤ N) :
    (down N (fun c => a * c + b) ^ n) ((upW N (fun c => a' * c + b') ^ n) (vacuum N R)) =
      ((n.factorial : R) * ∏ j ∈ range n, (b * b' + a * a' * j)) • vacuum N R :=
  down_pow_up_pow_sl2 _ _ _ (down_vacuum _) (a * a') (b * b') n
    (comm_level _ _ (fun m => b * b' + 2 * (a * a') * m) (fun ν hanti hlt => by
      rw [commutator_weighted_affine_affine hanti (not_full_of_sum_lt hlt)]
      push_cast; ring_nf) hn)

/-- **The z-measure normalisation**: up with weight `z + c`, down with `z' + c`, `n ≤ N`:
`D^n U^n e_∅ = n! (zz')_n e_∅`, the rising factorial. -/
theorem zmeasure_paths (z z' : R) {n : ℕ} (hn : n ≤ N) :
    (down N (fun c => z' + c) ^ n) ((upW N (fun c => z + c) ^ n) (vacuum N R)) =
      ((n.factorial : R) * ∏ j ∈ range n, (z * z' + j)) • vacuum N R := by
  have := sl2_paths (N := N) (R := R) 1 z' 1 z hn
  simp only [one_mul] at this
  rw [show (fun c : ℤ => z' + (c : R)) = fun c : ℤ => (c : R) + z' from funext fun _ => add_comm _ _,
    show (fun c : ℤ => z + (c : R)) = fun c : ℤ => (c : R) + z from funext fun _ => add_comm _ _,
    this]
  congr 2
  exact prod_congr rfl fun j _ => by ring

/-- **The fermionic twin**: up with weight `z − c`: `D^n U^n e_∅ = n! zz'(zz' − 1)⋯(zz' − n + 1) e_∅`,
the falling factorial (finite at `z = z' = k`: zero for `n > k²`). -/
theorem zmeasure_paths_twin (z z' : R) {n : ℕ} (hn : n ≤ N) :
    (down N (fun c => z' + c) ^ n) ((upW N (fun c => z - c) ^ n) (vacuum N R)) =
      ((n.factorial : R) * ∏ j ∈ range n, (z * z' - j)) • vacuum N R := by
  have := sl2_paths (N := N) (R := R) 1 z' (-1) z hn
  rw [show (fun c : ℤ => z' + (c : R)) = fun c : ℤ => 1 * (c : R) + z' from funext fun _ => by ring,
    show (fun c : ℤ => z - (c : R)) = fun c : ℤ => -1 * (c : R) + z from funext fun _ => by ring,
    this]
  congr 2
  exact prod_congr rfl fun j _ => by ring

end RMT.Symmetric.Corners
