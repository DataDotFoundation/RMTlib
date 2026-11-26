import RMTlib.Tableaux.MultisetHook.Generating
import RMTlib.Symmetric.OmegaCovariant

/-!
# Hooks divisible by `r` count the size the `r`-core loses (RMTlib#53 item 2)

`r · #{□ : r ∣ h(□)} = |λ| − |core_r(λ)|` (`card_hooks_dvd`): by Littlewood (`hooks_dvd`) the hooks
divisible by `r` are `r` times the hooks of the `r`-quotient, there is one hook per cell, and
`|λ| = |core| + r Σ_ρ |λ^ρ|` (`card_littlewood`). With `r = p^j` this makes the `p`-adic part of the
hook product a core statistic (the `p`-component of the idèle of `H(λ)`, #53 §2).
-/

open Finset

namespace RMT.MultisetHook

/-- **Hooks divisible by `r` count the size lost to the `r`-core**:
`r · #{□ : r ∣ h(□)} = |λ| − |core_r λ|`. -/
theorem card_hooks_dvd {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) :
    (r : ℤ) * (Multiset.card ((hooks μ).filter (fun h => (r : ℤ) ∣ h)) : ℤ) =
      μ.cells.card - (core r μ).cells.card := by
  rw [hooks_dvd hr, card_littlewood hr μ, ← Multiset.cardHom_apply, map_sum]
  simp only [Multiset.cardHom_apply, Multiset.card_map, card_hooks]
  push_cast
  ring

/-- The same, in `ℕ`: `#{□ : r ∣ h(□)} = (|λ| − |core_r λ|) / r`. -/
theorem card_hooks_dvd_eq_div {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) :
    Multiset.card ((hooks μ).filter (fun h => (r : ℤ) ∣ h)) =
      (μ.cells.card - (core r μ).cells.card) / r := by
  have h := card_hooks_dvd hr μ
  have hle : (core r μ).cells.card ≤ μ.cells.card := by
    have : (0 : ℤ) ≤ (r : ℤ) * (Multiset.card ((hooks μ).filter (fun h => (r : ℤ) ∣ h)) : ℤ) := by
      positivity
    omega
  have hd : r ∣ μ.cells.card - (core r μ).cells.card :=
    ⟨Multiset.card ((hooks μ).filter (fun h => (r : ℤ) ∣ h)), by zify [hle]; linarith⟩
  rw [eq_comm, Nat.div_eq_iff_eq_mul_left hr hd]
  zify [hle]; linarith


theorem hook_pos {μ : YoungDiagram} {h : ℤ} (hh : h ∈ hooks μ) : 0 < h := by
  obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hh
  have h1 := μ.mem_iff_lt_rowLen.mp hc
  have h2 := μ.mem_iff_lt_colLen.mp hc
  unfold hook; omega

/-- For positive naturals below `p^b`, the `p`-adic valuation of a product counts the pairs
(factor, `j`) with `p^j` dividing the factor. -/
theorem factorization_prod_eq_sum_card {p b : ℕ} (hp : p.Prime) (m : Multiset ℕ)
    (hm : ∀ n ∈ m, 0 < n ∧ n < p ^ b) :
    m.prod.factorization p = ∑ j ∈ Ico 1 b, Multiset.card (m.filter (p ^ j ∣ ·)) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ n ∈ m, 0 < n ∧ n < p ^ b := fun n hn => hm n (Multiset.mem_cons_of_mem hn)
    have hprod : m.prod ≠ 0 := by
      rw [Ne, Multiset.prod_eq_zero_iff]; intro h0; have := (hm' 0 h0).1; omega
    rw [Multiset.prod_cons, Nat.factorization_mul (by omega) hprod, Finsupp.add_apply, ih hm',
      Nat.factorization_eq_card_pow_dvd_of_lt hp ha.1 ha.2, card_filter, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [Multiset.filter_cons]
    split_ifs <;> simp; ring

/-- **The `p`-adic part of the hook product is a core statistic** (RMTlib#53 item 2):
`v_p ∏ h(□) = Σ_{1 ≤ j < b} (|λ| − |core_{p^j} λ|) / p^j`, for any `b` with every hook `< p^b`. -/
theorem padicValNat_prod_hooks {p : ℕ} [hp : Fact p.Prime] (μ : YoungDiagram) {b : ℕ}
    (hb : ∀ h ∈ hooks μ, h < (p : ℤ) ^ b) :
    padicValNat p ((hooks μ).map Int.toNat).prod =
      ∑ j ∈ Ico 1 b, (μ.cells.card - (core (p ^ j) μ).cells.card) / p ^ j := by
  have hm : ∀ n ∈ (hooks μ).map Int.toNat, 0 < n ∧ n < p ^ b := by
    intro n hn
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hn
    have h1 := hook_pos hh
    have h2 := hb h hh
    refine ⟨by omega, ?_⟩
    zify; rw [Int.toNat_of_nonneg h1.le]; exact h2
  rw [Nat.padicValNat_def, ← Nat.factorization_def _ hp.out, factorization_prod_eq_sum_card hp.out _ hm]
  refine sum_congr rfl fun j _ => ?_
  rw [← card_hooks_dvd_eq_div (pow_pos hp.out.pos j) μ, Multiset.filter_map, Multiset.card_map]
  congr 1
  refine Multiset.filter_congr fun h hh => ?_
  have h1 := hook_pos hh
  simp only [Function.comp_apply, Nat.cast_pow]
  rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg h1.le]
  push_cast; rfl

/-! ### ω on the abacus: the core of `λ′` is the conjugate of the core (#1 §3, #53) -/

/-- **Transposing reverses and conjugates the quotient, and negates the charges**: runner `ρ` of
`λ′` is runner `r − 1 − ρ` of `λ`, conjugated, with the opposite charge. -/
theorem quot_transpose {r : ℕ} (hr : 0 < r) (μ : YoungDiagram) {ρ : ℕ} (hρ : ρ < r) :
    qcharge r μ.transpose ρ = -qcharge r μ (r - 1 - ρ) ∧
      quot r μ.transpose ρ = (quot r μ (r - 1 - ρ)).transpose := by
  have hσ : ((r - 1 - ρ : ℕ) : ℤ) = r - 1 - ρ := by omega
  refine maya_unique (M := fun y => Occ μ.transpose (r * y + ρ))
    (fun x => quot_spec hr μ.transpose ρ x) (fun x => ?_)
  rw [occ_transpose, quot_spec hr, occ_transpose, not_iff_not]
  constructor <;> intro h <;> convert h using 2 <;> rw [hσ] <;> ring

/-- **ω at every place on the abacus: `core_r(λ′) = core_r(λ)′`** (for every `r`; the `0`-core is
empty). -/
theorem core_transpose (r : ℕ) (μ : YoungDiagram) :
    core r μ.transpose = (core r μ).transpose := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [core, lt_irrefl, dite_false]
    ext c; simp [YoungDiagram.mem_transpose]
  apply eq_of_occ
  intro x
  rw [core_spec hr, occ_transpose, core_spec hr]
  obtain ⟨hxd, hxr⟩ := runner_decomp hr x
  set ρ := (x % r).toNat
  set m := x / r
  have hσ : r - 1 - ρ < r := by omega
  have hx' : -1 - x = r * (-m - 1) + ((r - 1 - ρ : ℕ) : ℤ) := by
    rw [show ((r - 1 - ρ : ℕ) : ℤ) = r - 1 - ρ by omega]; rw [hxd]; ring
  rw [hx', coreSet_runner hr _ hσ, hxd, coreSet_runner hr _ hxr, occ_bot, occ_bot,
    (quot_transpose hr μ hxr).1]
  omega

/-- **The `r`-core is `ω`-covariant**, with no change of parameter: `core_r(λ′) = core_r(λ)′`. -/
def omegaCore : RMT.Symmetric.OmegaCovariant (fun (r : ℕ) (μ : YoungDiagram) => core r μ) where
  twin := id
  twin_involutive _ := rfl
  out _ ν := ν.transpose
  out_transpose_out _ ν := YoungDiagram.transpose_transpose ν
  map_transpose r μ := core_transpose r μ

end RMT.MultisetHook
