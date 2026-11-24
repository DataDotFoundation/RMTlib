import Mathlib

/-!
# The multiset hook length formula (Dehaye–Han, arXiv:1104.5435, Theorem 1)

This file states Theorem 1 in the paper's form, as the `Prop` `RMT.MultisetHook.Theorem1`, and
proves the character corollary. The theorem itself is `RMT.MultisetHook.theorem1`
(`MultisetHook/Bijection.lean`), proved through the restatement outlined in
`MultisetHook/Outline.lean`. Numerical checks of the examples are in
`scripts/multiset_hook_check.py`.

## Coverage of the paper

| Paper | Lean | Status |
|---|---|---|
| Thm 1, Eqs. (1)–(2), Lemma 3 (4)–(8) | `theorem1`, `Statement` | proved |
| Cor 4, Eq. (19) | `corollary4` | proved |
| Thm 11 (Macdonald), specialised | `MacdonaldSpec` | stated (cited in the paper) |
| Lemma 12, Eqs. (33)–(34) | `sin_sub_mul_sin_add`, `prod_sin_sub` | proved |
| Lemma 13 | `Lemma13`; `lemma13_iff_macdonaldSpec` | stated; ⇔ Thm 11 proved |
| Lemma 14, Thm 5, Thm 2 | `Lemma14`, `Theorem5`, `Theorem2` | stated |
| Thm 5, "basic fact" | `exists_hook_eq_of_not_core` | proved |
| Thm 15 (Han–Ji) | `Theorem15`; `hanJi_comb`, `littlewood`, `hooks_dvd`, `card_littlewood` | stated; combinatorial form proved |
| Thm 16 (hook-content) | `Theorem16` | stated (cited in the paper) |
| Thm 17, Eqs. (40)–(41) | `psi_bijective`, `eq40`, `eq41` | proved |
| Cor 6–10 | `Corollary6` … `Corollary10` | stated |

The stated `q`-series results are checked numerically in `scripts/multiset_hook_check.py`.

## The statement, in its universal form

Theorem 1 of the paper holds for *every* weight `τ : ℤ → F`. The underlying fact is an identity
in the free abelian group `ℤ^(ℤ)` on the integers, so we state it there, as an equation of
multisets with all terms moved to the side where they are positive:

  `{h − t} + {h + t} + ∑_{i=1}^{t−1} (β_i + t − i)·{i}
     = 2·{h} + ∑_{i=1}^{t−1} β_i·{−i} + {v_i − v_j : i < j}`

(`h` runs over the hook multiset `H(λ)` and `β_i = #{□ : h(□) = t − i}`). The paper's Eq. (2) is
the image of this under the character `[k] ↦ τ(k)`. We prove that step (`Statement.character`)
for `τ` with values in any commutative group `G`, for example `Fˣ`. That removes the hypothesis
the paper leaves implicit: Eq. (2) divides by `τ(h)²` and `τ(i)`, which can vanish (for example
`τ = sin(·z)` with `z = π/h`).

## Conventions

* Partitions are Mathlib `YoungDiagram`s, with the cell `(i, j)` in row `i` and column `j`,
  both counted from `0`.
* The Maya site of row `i` is `b_i = λ_i − i − 1`, as in `RMT.Fermion` (`Fermion/Maya.lean`),
  so the empty partition is the Dirac sea `{b ≤ −1}`. The paper's `W`-set is
  `{b_i + (t + 1)/2}`, so its `V`-coding is `vCoding = aCoding + (t + 1)/2` (`ℚ`-valued: it
  lies in `ℤ + ½` when `t` is even).
* The coding is defined from the set `V(λ) = {x ∈ M : x + t ∉ M}` of `t`-maximal sites
  (`vSet`), enumerated in decreasing order (`aCoding`).
* Eq. (2) involves only the differences `v_i − v_j`, so its divisor form uses the integer
  coding `aCoding`. The shift `(t + 1)/2` matters only for Eqs. (1) and (8).

## A correction to the paper

The paper's condition (i) on a `V_t`-coding reads `{v_i − i mod t} = t₀ + {0, …, t − 1}`. This
is false as printed. For `t = 2`, the empty partition (a 2-core) has `V = (½, −½)`, and
`v₀ − 0 = ½ ≡ −3/2 = v₁ − 1 (mod 2)`. In fact no vector with `t = 2` satisfies the printed
condition. The correct condition, used in `IsVCoding`, is that the `v_i` represent every
class of `t₀ + ℤ` modulo `t` (equivalently: are pairwise incongruent).

## Boson/fermion twin

Conjugation `λ ↦ λᵀ` acts on codings by `V ↦ −V` (the paper's Eq. (6)). It preserves the hook
multiset, hence `β`, and therefore the divisor identity. We include it in `Theorem1` as the
field `transpose`, so the statement is ω-covariant.
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

/-! ### Hooks and cores -/

/-- The hook length of the cell `c = (i, j)` of `μ`: arm + leg + 1, as an integer. -/
def hook (μ : YoungDiagram) (c : ℕ × ℕ) : ℤ :=
  (μ.rowLen c.1 : ℤ) - c.2 + μ.colLen c.2 - c.1 - 1

/-- The hook length multiset `H(λ)`. -/
def hooks (μ : YoungDiagram) : Multiset ℤ := μ.cells.val.map (hook μ)

/-- `λ` is a `t`-core: no hook length is divisible by `t`. -/
def IsTCore (t : ℕ) (μ : YoungDiagram) : Prop := ∀ h ∈ hooks μ, ¬ (t : ℤ) ∣ h

instance (t : ℕ) (μ : YoungDiagram) : Decidable (IsTCore t μ) := by
  unfold IsTCore; infer_instance

/-- `β_i(λ) = #{□ ∈ λ : h(□) = t − i}`. -/
def beta (t : ℕ) (μ : YoungDiagram) (i : ℕ) : ℕ := (hooks μ).count ((t : ℤ) - i)

/-! ### The `V`-coding -/

/-- The Maya site (particle) `b_i = λ_i − i − 1` of row `i` (the convention of `RMT.Fermion`). -/
def site (μ : YoungDiagram) (i : ℕ) : ℤ := (μ.rowLen i : ℤ) - i - 1

/-- The hole `j − λ'_j` of column `j`: the empty site that column `j` contributes. -/
def hole (μ : YoungDiagram) (j : ℕ) : ℤ := (j : ℤ) - μ.colLen j

/-- The Maya diagram `M(λ) = {b_i}`: `x` is an occupied site. -/
def Occ (μ : YoungDiagram) (x : ℤ) : Prop := ∃ i, site μ i = x

/-- **The `V`-set** `V(λ) = {x ∈ M : x + t ∉ M}`, the `t`-maximal occupied sites. (They lie in the
window `[−ℓ(λ) − t, λ₁]`, which only serves to make the set finite.) -/
noncomputable def vSet (t : ℕ) (μ : YoungDiagram) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(μ.colLen 0 : ℤ) - t) (μ.rowLen 0)).filter fun x => Occ μ x ∧ ¬ Occ μ (x + t)

open Classical in
/-- The `t`-maximal sites, sorted in decreasing order: the unshifted coding `a` (`0` if `V(λ)` does
not have `t` elements, which does not happen for `t`-cores). -/
noncomputable def aCoding (t : ℕ) (μ : YoungDiagram) : Fin t → ℤ :=
  if h : (vSet t μ).card = t then fun i => (vSet t μ).orderEmbOfFin h i.rev else 0

/-- **The paper's `V_t`-coding `φ_t(λ)`**: `v_i = a_i + (t + 1)/2`, in `t₀ + ℤ`. -/
def vCoding (t : ℕ) (μ : YoungDiagram) : Fin t → ℚ := fun i => aCoding t μ i + ((t : ℚ) + 1) / 2

/-- **`V_t`-codings** (with condition (i) corrected): strictly decreasing, summing to `0`, in
`t₀ + ℤ` (that is, `v_i − (t + 1)/2 ∈ ℤ`), and pairwise incongruent mod `t`. -/
def IsVCoding (t : ℕ) (v : Fin t → ℚ) : Prop :=
  StrictAnti v ∧ ∑ i, v i = 0 ∧
    ∃ k : Fin t → ℤ, (∀ i, v i = k i + ((t : ℚ) + 1) / 2) ∧
      ∀ i j, k i ≡ k j [ZMOD t] → i = j

/-! ### The two sides of the divisor identity -/

/-- The differences `{a_i − a_j : i < j}` (with `t = 0` this is empty). -/
def pairDiffs {t : ℕ} (a : Fin t → ℤ) : Multiset ℤ :=
  ((univ : Finset (Fin t × Fin t)).filter fun p => p.1 < p.2).val.map fun p => a p.1 - a p.2

/-- Left side of the divisor form of Eq. (2): `{h − t} + {h + t} + ∑ (β_i + t − i)·{i}`. -/
def divisorLHS (t : ℕ) (μ : YoungDiagram) : Multiset ℤ :=
  (hooks μ).map (· - (t : ℤ)) + (hooks μ).map (· + (t : ℤ)) +
    ∑ i ∈ Ico (1 : ℕ) t, (beta t μ i + t - i) • ({(i : ℤ)} : Multiset ℤ)

/-- Right side of the divisor form of Eq. (2): `2·{h} + ∑ β_i·{−i} + {v_i − v_j : i < j}`. -/
def divisorRHS (t : ℕ) (μ : YoungDiagram) : Multiset ℤ :=
  2 • hooks μ + ∑ i ∈ Ico (1 : ℕ) t, beta t μ i • ({-(i : ℤ)} : Multiset ℤ) + pairDiffs (aCoding t μ)

/-! ### Theorem 1 -/

/-- **Dehaye–Han, Theorem 1, at a fixed `t`**, in universal (divisor) form, with its ω-twin. -/
structure Statement (t : ℕ) : Prop where
  /-- `φ_t` maps `t`-cores to `V_t`-codings. -/
  coding : ∀ μ, IsTCore t μ → IsVCoding t (vCoding t μ)
  /-- `φ_t` is a bijection from `t`-cores onto `V_t`-codings. -/
  bijective : ∀ v, IsVCoding t v → ∃! μ, IsTCore t μ ∧ vCoding t μ = v
  /-- Eq. (1): `|λ| = (1/2t) ∑ v_i² − (t² − 1)/24`; the constant is `dim sl_t / 24`. -/
  size : ∀ μ, IsTCore t μ →
    (μ.cells.card : ℚ) = (∑ i, vCoding t μ i ^ 2) / (2 * t) - ((t : ℚ) ^ 2 - 1) / 24
  /-- Eq. (2), universal form: an identity in `ℤ^(ℤ)`, before choosing any weight `τ`. -/
  divisor : ∀ μ, IsTCore t μ → divisorLHS t μ = divisorRHS t μ
  /-- Eq. (6), the boson/fermion twin: conjugation acts on codings by `V ↦ −V`. -/
  transpose : ∀ μ, IsTCore t μ → vCoding t μ.transpose = fun i => -vCoding t μ i.rev

/-- **Dehaye–Han, Theorem 1**, for every `t ≥ 1`. -/
def Theorem1 : Prop := ∀ t, 0 < t → Statement t

/-! ### Eq. (2) for an arbitrary weight -/

section Character

variable {G : Type*} [CommGroup G] (τ : ℤ → G)

/-- Evaluating a divisor on the weight `τ`: `m ↦ ∏_{k ∈ m} τ(k)`, an additive map into
`Additive G`. -/
def eval : Multiset ℤ →+ Additive G where
  toFun m := Additive.ofMul (m.map τ).prod
  map_zero' := by simp
  map_add' m n := by simp [Multiset.map_add, Multiset.prod_add]

theorem eval_apply (m : Multiset ℤ) : (eval τ m).toMul = (m.map τ).prod := rfl

theorem eval_nsmul (k : ℕ) (m : Multiset ℤ) : (eval τ (k • m)).toMul = ((m.map τ).prod) ^ k := by
  rw [map_nsmul, toMul_nsmul, eval_apply]

theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → Multiset ℤ) :
    (eval τ (∑ i ∈ s, f i)).toMul = ∏ i ∈ s, (eval τ (f i)).toMul := by
  rw [map_sum, toMul_sum]

/-- Rearranging `A·B·X = C²·Y·P` in a commutative group (via `Additive` and `abel`). -/
theorem rearrange (A B C X Y P : G) (e : A * B * X = C ^ 2 * Y * P) :
    A * B / C ^ 2 = Y / X * P := by
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at e' ⊢
  rw [← sub_eq_zero]
  calc _ = (Additive.ofMul A + Additive.ofMul B + Additive.ofMul X) -
        (2 • Additive.ofMul C + Additive.ofMul Y + Additive.ofMul P) := by abel
    _ = 0 := by rw [e', sub_self]

/-- **The paper's Eq. (2)**, for a weight `τ` with values in a commutative group (e.g. `Fˣ`):
the universal identity `Statement.divisor`, evaluated on `τ`. -/
theorem Statement.character {t : ℕ} (H : Statement t) (μ : YoungDiagram) (hμ : IsTCore t μ) :
    ((hooks μ).map fun h => τ (h - (t : ℤ)) * τ (h + (t : ℤ)) / τ h ^ 2).prod =
      (∏ i ∈ Ico (1 : ℕ) t, τ (-(i : ℤ)) ^ beta t μ i / τ i ^ (beta t μ i + t - i)) *
        ((pairDiffs (aCoding t μ)).map τ).prod := by
  have e := congrArg (fun m => (eval τ m).toMul) (H.divisor μ hμ)
  simp only [divisorLHS, divisorRHS, map_add, toMul_add] at e
  rw [eval_sum, eval_sum, eval_nsmul] at e
  simp only [eval_apply, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
    Multiset.prod_singleton, Multiset.map_map, Function.comp_def] at e
  rw [Multiset.prod_map_div, Multiset.prod_map_mul, Multiset.prod_map_pow, prod_div_distrib]
  exact rearrange _ _ _ _ _ _ e

end Character

end

end RMT.MultisetHook
