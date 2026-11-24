import RMTlib.Tableaux.SquareCount
import RMTlib.Tableaux.Complement

/-!
# Theorem 3 of Dehaye (arXiv:1201.4478) for U(N): the statement

For a Haar-random `U ∈ U(N)`, `𝔼|det(1 − U)|^{2k} = ∏_{i,j ≤ k} (N + i + j − 1)/(i + j − 1)`
(Keating–Snaith, Bump–Gamburd), a polynomial of degree `k²` in `N`. Theorem 3, with the U(N)
arithmetic data in place of those of `ζ`, writes the coefficient of `N^{k² − M}` as a path count
in Young's lattice cut off by the `k × k` square:

  `c_M(k) = 1/(k² − M)! · Σ_{|κ| + |λ| = M} d_κλ · dim(λ, S_k(κ))`.

* `d_κλ = (−1)^{|λ|} [a^{κ+δ} b^{λ+δ}] Δ(a) Δ(b) ∏_{i,j} g(a_i − b_j)` with
  `g(u) = u/(1 − e^{−u})` (the U(N) kernel `1/(1 − e^{−u})` times `u`), `δ = (k−1, …, 0)` and
  `Δ` the Vandermonde product; equivalently, `(−1)^{|λ|}` times the coefficient of `s_κ(a) s_λ(b)`
  in `∏ g(a_i − b_j)`.
* `dim(λ, μ)` is the number of paths `λ → μ` in Young's lattice (`skewDim`).
* `S_k(κ)` is the transpose of the rotated complement of `κ` in the square (`S`); `κ` and
  `S_k(κ)` are complementary in the sense of Lemma 6 (`RMT.lemma6`).

Everything is computable: `thm3Coeff k M` is the right side, `exactCoeff k M` the coefficient of
the exact moment polynomial `momentPoly k`. The statement is `RMT.UN.Theorem3`. It is
the same computation as `scripts/un_test.py` (variant `transpose`).

## Main definitions
* `RMT.UN.thm3Coeff`, `RMT.UN.exactCoeff`, `RMT.UN.momentPoly`.
* `RMT.UN.Theorem3`: `thm3Coeff k M = (momentPoly k).coeff (k² − M)` for `M ≤ k²`.

## Status
* Proved for `M = 0` and `M = 1` and every `k` (`RMT.UN.theorem3_zero`, `RMT.UN.theorem3_one`,
  `RMTlib/Moments/Theorem3UNLow.lean`).
* Checked by `#guard`, exactly in `ℚ`: every `M` for `k ≤ 3`, `M ≤ 4` for `k = 4`, `M ≤ 2` for
  `k = 5` (`RMTlibExamples/Theorem3UN.lean`; `k ≤ 2` below). By `#eval` also `M ≤ 8` for
  `k = 4` and `M ≤ 4` for `k = 5` (about 90 s, not run in CI).
* Open in general. RMTlib has no `sorry`, so the open target (`RMT.Targets.theorem3UN`) is kept
  outside this library.

## Evaluation
`prodCoef` and `skewDim` are the plain recursions (a sum over the expansion of the product, and
a sum over paths). The checks use `thm3CoeffFast`, which tabulates both (`memo`, `prodCoefMemo`,
`skewMemo`) and is proved equal to `thm3Coeff` (`thm3CoeffFast_eq`).
-/

open Finset Polynomial
open scoped Nat

namespace RMT.UN

/-- `h_j = (−1)^j/(j+1)!`, the Taylor coefficients of `(1 − e^{−u})/u`. -/
def hCoeff (j : ℕ) : ℚ := (-1) ^ j / ((j + 1)! : ℚ)

/-- `gTable n = [g_n, …, g_0]`, where `g(u) = u/(1 − e^{−u}) = Σ g_n uⁿ`, from `g · h = 1`. -/
def gTable : ℕ → List ℚ
  | 0 => [1]
  | n + 1 =>
    let t := gTable n
    (-(∑ j ∈ range (n + 1), hCoeff (j + 1) * t.getD j 0)) :: t

/-- The `n`-th Taylor coefficient `g_n` of `g(u) = u/(1 − e^{−u})`. -/
def gCoeff (n : ℕ) : ℚ := (gTable n).headD 0

/-- The weight of `a^p b^q` in `g(a − b) = Σ_n g_n (a − b)ⁿ`. -/
def wt (g : ℕ → ℚ) (p q : ℕ) : ℚ := g (p + q) * ((p + q).choose p : ℚ) * (-1) ^ q

variable {k : ℕ}

/-- The exponents of `a_i` allowed at a cell: everything up to what is left, `0, …, n`, or, if
no later cell carries `a_i` (`last = true`), exactly what is left. -/
def expRange (last : Bool) (n : ℕ) : Finset ℕ := if last then {n} else range (n + 1)

/-- The coefficient of `a^α b^β` in `∏_{(i,j) ∈ cs} g(a_i − b_j)`. At the last cell of a row
(column) the exponent of `a_i` (`b_j`) is forced. -/
def prodCoef (g : ℕ → ℚ) : List (Fin k × Fin k) → (Fin k → ℕ) → (Fin k → ℕ) → ℚ
  | [], α, β => if (∀ i, α i = 0) ∧ (∀ j, β j = 0) then 1 else 0
  | c :: cs, α, β =>
    ∑ p ∈ expRange (!cs.any (·.1 == c.1)) (α c.1),
      ∑ q ∈ expRange (!cs.any (·.2 == c.2)) (β c.2),
        wt g p q * prodCoef g cs (Function.update α c.1 (α c.1 - p))
          (Function.update β c.2 (β c.2 - q))

/-- The cells of the `k × k` square. -/
def cells (k : ℕ) : List (Fin k × Fin k) :=
  (List.finRange k).flatMap fun i => (List.finRange k).map fun j => (i, j)

/-- `δ_i = k − 1 − i`. -/
def delta (k : ℕ) (i : Fin k) : ℕ := k - 1 - i

/-- The exponent `κ + δ − σ(δ)`, `i ↦ κ_i + δ_i − δ_{σ i}`, in `ℤ`. -/
def shiftExp (κ : Fin k → ℕ) (σ : Equiv.Perm (Fin k)) : Fin k → ℤ :=
  fun i => (κ i : ℤ) + delta k i - delta k (σ i)

/-- A coefficient function `F(α, β)` extended by zero to negative exponents. -/
def coefZ (F : (Fin k → ℕ) → (Fin k → ℕ) → ℚ) (α β : Fin k → ℤ) : ℚ :=
  if (∀ i, 0 ≤ α i) ∧ (∀ j, 0 ≤ β j) then F (fun i => (α i).toNat) (fun j => (β j).toNat) else 0

/-- The arithmetic datum `d_κλ = (−1)^{|λ|} [a^{κ+δ} b^{λ+δ}] Δ(a) Δ(b) f~(a; b)`, where
`F(α, β) = [a^α b^β] f~` and `Δ(a) = ∏_{i<j}(a_i − a_j) = Σ_σ sgn σ · a^{σ(δ)}`. -/
def dCoef (F : (Fin k → ℕ) → (Fin k → ℕ) → ℚ) (κ lam : Fin k → ℕ) : ℚ :=
  (-1) ^ (∑ i, lam i) * ∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k),
    ((Equiv.Perm.sign σ : ℤ) : ℚ) * ((Equiv.Perm.sign τ : ℤ) : ℚ) *
      coefZ F (shiftExp κ σ) (shiftExp lam τ)

/-- The number of paths `λ → μ` in Young's lattice (standard tableaux of skew shape `μ/λ`),
removing corners from `μ`; `fuel ≥ |μ| − |λ|`. -/
def skewDim (lam : Fin k → ℕ) : ℕ → (Fin k → ℕ) → ℕ
  | 0, mu => if mu = lam then 1 else 0
  | f + 1, mu => if mu = lam then 1 else
      ∑ i ∈ univ.filter (fun i => IsCorner mu i ∧ ∀ j, lam j ≤ removeBox mu i j),
        skewDim lam f (removeBox mu i)

/-- `S_k(κ)`: the transpose of the rotated complement `i ↦ k − κ_{k−1−i}` of `κ` in the square. -/
def S (k : ℕ) (κ : Fin k → ℕ) : Fin k → ℕ := fun j => tr (fun i => k - κ (Fin.rev i)) j

/-- Partitions of `m` in the `k × k` box. -/
def boxParts (k m : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => range (k + 1)).filter
    fun κ => (∀ i j : Fin k, i ≤ j → κ j ≤ κ i) ∧ ∑ i, κ i = m

/-- Read the `n`-th entry of a list of coefficients. -/
@[noinline] def gLookup (t : List ℚ) (n : ℕ) : ℚ := t.getD n 0

/-- `g` read from the table `[g_0, …, g_D]` (`g_n` for `n ≤ D`). -/
def gFun (D : ℕ) : ℕ → ℚ := gLookup (gTable D).reverse

/-- The Taylor coefficients `F(α, β) = [a^α b^β] f~(a; b)` of the U(N) function
`f~(a; b) = ∏_{i,j ≤ k} g(a_i − b_j)`. -/
def fCoef (k : ℕ) : (Fin k → ℕ) → (Fin k → ℕ) → ℚ := prodCoef (gFun (k * k)) (cells k)

/-- `1/(k² − M)! · Σ_{|κ| + |λ| = M} d_κλ · dim(λ, S_k(κ))` for Taylor coefficients `F` and
a path count `dim λ fuel μ`. -/
def thm3CoeffWith (F : (Fin k → ℕ) → (Fin k → ℕ) → ℚ)
    (dim : (Fin k → ℕ) → ℕ → (Fin k → ℕ) → ℚ) (M : ℕ) : ℚ :=
  1 / ((k * k - M)! : ℚ) * ∑ m ∈ range (M + 1), ∑ κ ∈ boxParts k m, ∑ lam ∈ boxParts k (M - m),
    dCoef F κ lam * dim lam (k * k - m - (M - m)) (S k κ)

/-- **The right side of Theorem 3** (U(N) data):
`c_M(k) = 1/(k² − M)! · Σ_{|κ| + |λ| = M} d_κλ · dim(λ, S_k(κ))`. -/
def thm3Coeff (k M : ℕ) : ℚ := thm3CoeffWith (fCoef k) (fun lam f mu => skewDim lam f mu) M

/-- The multiset of weights `i + j − 1`, `1 ≤ i, j ≤ k`. -/
def weights (k : ℕ) : Multiset ℚ :=
  (univ : Finset (Fin k × Fin k)).val.map fun c => ((c.1 : ℕ) + c.2 + 1 : ℚ)

/-- The coefficient of `N^{k² − M}` in `∏_{i,j ≤ k} (N + i + j − 1)/(i + j − 1)`. -/
def exactCoeff (k M : ℕ) : ℚ := (weights k).esymm M / (weights k).prod

/-- **The U(N) moment polynomial** `∏_{i,j ≤ k} (N + i + j − 1)/(i + j − 1)`, in the variable
`N = X`. -/
noncomputable def momentPoly (k : ℕ) : ℚ[X] :=
  C ((weights k).prod)⁻¹ * ((weights k).map fun r => X + C r).prod

/-- **Theorem 3 of Dehaye (arXiv:1201.4478), U(N) case**: for `M ≤ k²` the coefficient of
`N^{k² − M}` in the moment polynomial is `1/(k² − M)! · Σ_{|κ|+|λ|=M} d_κλ · dim(λ, S_k(κ))`. -/
def Theorem3 : Prop :=
  ∀ k M : ℕ, M ≤ k * k → thm3Coeff k M = (momentPoly k).coeff (k * k - M)

theorem card_weights (k : ℕ) : Multiset.card (weights k) = k * k := by
  simp [weights]

/-- The coefficients of `momentPoly` are `exactCoeff`. -/
theorem momentPoly_coeff (k M : ℕ) (hM : M ≤ k * k) :
    (momentPoly k).coeff (k * k - M) = exactCoeff k M := by
  rw [momentPoly, coeff_C_mul, Multiset.prod_X_add_C_coeff _ (by rw [card_weights]; omega),
    card_weights, Nat.sub_sub_self hM, exactCoeff, div_eq_inv_mul]

theorem theorem3_iff : Theorem3 ↔ ∀ k M : ℕ, M ≤ k * k → thm3Coeff k M = exactCoeff k M :=
  forall_congr' fun k => forall_congr' fun M => imp_congr_right fun hM => by
    rw [momentPoly_coeff k M hM]

/-! ### A memoised evaluation

`prodCoef` recomputes the same coefficients many times and `skewDim` enumerates paths one by one.
`thm3CoeffFast` tabulates each partial product and each level of the path count once (`memo`),
and is proved equal to `thm3Coeff` (`thm3CoeffFast_eq`). The tables are structures (`Tab`) and
the table-building steps are `@[noinline]`, so that the compiler does not inline a table into the
function that reads it (which would rebuild it at every read). -/

/-- A memo table: values stored in a hash map, with a fallback for the keys not stored. -/
structure Tab (α : Type) [BEq α] [Hashable α] where
  /-- The stored values. -/
  map : Std.HashMap α ℚ
  /-- The function the table memoises. -/
  fallback : α → ℚ

/-- Read a memo table. -/
def Tab.get {α : Type} [BEq α] [Hashable α] (t : Tab α) (x : α) : ℚ :=
  match t.map[x]? with
  | some v => v
  | none => t.fallback x

/-- Memoise `φ` on `keys`; off `keys` the value is recomputed, so `(memo keys φ).get = φ`. -/
def memo {α : Type} [BEq α] [Hashable α] (keys : List α) (phi : α → ℚ) : Tab α :=
  ⟨keys.foldl (fun m x => m.insert x (phi x)) ∅, phi⟩

theorem memo_eq {α : Type} [BEq α] [LawfulBEq α] [Hashable α] (keys : List α) (phi : α → ℚ) :
    (memo keys phi).get = phi := by
  have key : ∀ (l : List α) (m : Std.HashMap α ℚ), (∀ y v, m[y]? = some v → v = phi y) →
      ∀ y v, (l.foldl (fun m x => m.insert x (phi x)) m)[y]? = some v → v = phi y := by
    intro l
    induction l with
    | nil => intro m hm; exact hm
    | cons x l ih =>
      intro m hm
      refine ih _ fun y v hv => ?_
      rw [Std.HashMap.getElem?_insert] at hv
      split at hv
      · next h => rw [eq_of_beq h] at hv; exact (Option.some.inj hv).symm
      · exact hm y v hv
  funext x
  simp only [memo, Tab.get]
  split
  · next v hv => exact key keys ∅ (fun y v h => by simp at h) x v hv
  · rfl

/-- Hash a vector through its list of entries. -/
instance instHashableVec : Hashable (Fin k → ℕ) := ⟨fun f => hash (List.ofFn f)⟩

/-- The vectors in `ℕ^k` of total at most `D` (as lists). -/
def vecsLe : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | r + 1, D => (List.range (D + 1)).flatMap fun a => (vecsLe r (D - a)).map (a :: ·)

/-- The pairs `(α, β)` of total degree at most `D`: the keys of the memo tables. -/
def memoKeys (k D : ℕ) : List ((Fin k → ℕ) × (Fin k → ℕ)) :=
  (vecsLe (2 * k) D).map fun l => (fun i => l.getD i 0, fun j => l.getD (k + j) 0)

/-- One cell of `prodCoef`, tabulated on `keys`, from the table `F` of the remaining cells. -/
@[noinline] def memoStep (g : ℕ → ℚ) (keys : List ((Fin k → ℕ) × (Fin k → ℕ)))
    (c : Fin k × Fin k) (cs : List (Fin k × Fin k)) (F : Tab ((Fin k → ℕ) × (Fin k → ℕ))) :
    Tab ((Fin k → ℕ) × (Fin k → ℕ)) :=
  memo keys fun x =>
    ∑ p ∈ expRange (!cs.any (·.1 == c.1)) (x.1 c.1),
      ∑ q ∈ expRange (!cs.any (·.2 == c.2)) (x.2 c.2),
        wt g p q * F.get (Function.update x.1 c.1 (x.1 c.1 - p),
          Function.update x.2 c.2 (x.2 c.2 - q))

/-- `prodCoef`, with every partial product tabulated on `keys`. -/
def prodCoefMemo (g : ℕ → ℚ) (keys : List ((Fin k → ℕ) × (Fin k → ℕ))) :
    List (Fin k × Fin k) → Tab ((Fin k → ℕ) × (Fin k → ℕ))
  | [] => ⟨∅, fun x => prodCoef g [] x.1 x.2⟩
  | c :: cs => memoStep g keys c cs (prodCoefMemo g keys cs)

theorem prodCoefMemo_eq (g : ℕ → ℚ) (keys : List ((Fin k → ℕ) × (Fin k → ℕ)))
    (cs : List (Fin k × Fin k)) : (prodCoefMemo g keys cs).get = fun x => prodCoef g cs x.1 x.2 := by
  induction cs with
  | nil => funext x; simp [prodCoefMemo, Tab.get]
  | cons c cs ih =>
    funext x
    simp only [prodCoefMemo, memoStep, memo_eq, ih]
    rfl

/-- One level of `skewDim`, tabulated on `keys`, from the table `T` of the level below. -/
@[noinline] def skewStep (lam : Fin k → ℕ) (keys : List (Fin k → ℕ)) (T : Tab (Fin k → ℕ)) :
    Tab (Fin k → ℕ) :=
  memo keys fun mu => if mu = lam then 1 else
    ∑ i ∈ univ.filter (fun i => IsCorner mu i ∧ ∀ j, lam j ≤ removeBox mu i j),
      T.get (removeBox mu i)

/-- `skewDim lam f`, tabulated level by level on `keys`. -/
def skewMemo (lam : Fin k → ℕ) (keys : List (Fin k → ℕ)) : ℕ → Tab (Fin k → ℕ)
  | 0 => ⟨∅, fun mu => if mu = lam then 1 else 0⟩
  | f + 1 => skewStep lam keys (skewMemo lam keys f)

theorem skewMemo_eq (lam : Fin k → ℕ) (keys : List (Fin k → ℕ)) (f : ℕ) :
    (skewMemo lam keys f).get = fun mu => (skewDim lam f mu : ℚ) := by
  induction f with
  | zero => funext mu; simp [skewMemo, Tab.get, skewDim]
  | succ f ih =>
    funext mu
    simp only [skewMemo, skewStep, memo_eq, ih, skewDim]
    split <;> simp

/-- `thm3Coeff`, computed with memo tables. -/
def thm3CoeffFast (k M : ℕ) : ℚ :=
  let T := prodCoefMemo (gLookup (gTable (k * k)).reverse) (memoKeys k M) (cells k)
  thm3CoeffWith (fun α β => T.get (α, β))
    (fun lam f mu => (skewMemo lam (boxPartitions k) f).get mu) M

theorem thm3CoeffFast_eq (k M : ℕ) : thm3CoeffFast k M = thm3Coeff k M := by
  simp only [thm3CoeffFast, prodCoefMemo_eq, skewMemo_eq]; rfl

-- Evidence: Theorem 3 holds exactly for `k ≤ 2` (`k = 3`: `RMTlibExamples/Theorem3UN.lean`).
#guard (List.range 3).all fun k => (List.range (k * k + 1)).all fun M =>
  thm3CoeffFast k M == exactCoeff k M

end RMT.UN
