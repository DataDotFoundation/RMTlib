import RMTlib.KeatingSnaith.Constant

/-!
# Standard Young tableaux of the square

`gSYT k` counts the standard Young tableaux of the `k × k` square (1, 1, 2, 42, 24024, …).
The hook-length formula (Frame–Robinson–Thrall) gives `g_k = (k²)! · ksConst k`. It is stated
here as `HookLengthSquare` and checked for small `k`; the general proof is
`RMT.hookLengthSquare_holds` (`RMTlib/Tableaux/SquareCount.lean`).

## Main results
* `RMT.gSYT_one`, `RMT.gSYT_two`: the definition gives the right small counts.
* `RMT.hookLengthSquare_iff`: the target, cleared of denominators.
* `RMT.hookLengthSquare_lt_three`: the target holds for `k < 3`.
-/

open Finset
open scoped Nat

namespace RMT

/-- A standard Young tableau of the `k × k` square: a bijective filling with `0, …, k² − 1`,
increasing along rows and down columns. -/
def IsSquareSYT (k : ℕ) (f : Fin k × Fin k → Fin (k * k)) : Prop :=
  Function.Bijective f ∧ (∀ i j j', j < j' → f (i, j) < f (i, j')) ∧
    (∀ i i' j, i < i' → f (i, j) < f (i', j))

instance (k : ℕ) : DecidablePred (IsSquareSYT k) := fun _ => by
  unfold IsSquareSYT; infer_instance

/-- The number `g_k` of standard Young tableaux of the `k × k` square. -/
def gSYT (k : ℕ) : ℕ := Fintype.card {f // IsSquareSYT k f}

theorem gSYT_one : gSYT 1 = 1 := by decide

theorem gSYT_two : gSYT 2 = 2 := by decide

/-- The hook-length formula for squares: `g_k = (k²)! · ∏_{j<k} j!/(j+k)!`. -/
def HookLengthSquare : Prop := ∀ k : ℕ, (gSYT k : ℚ) = ((k * k) ! : ℕ) * ksConst k

/-- The hook-length formula at `k`, cleared of denominators. -/
theorem hookLengthSquare_iff (k : ℕ) :
    (gSYT k : ℚ) = ((k * k) ! : ℕ) * ksConst k ↔
      gSYT k * ∏ j ∈ range k, (j + k) ! = (k * k) ! * ∏ j ∈ range k, j ! := by
  have hB : (∏ j ∈ range k, (((j + k) ! : ℕ) : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [ksConst_eq_div, mul_div_assoc', eq_div_iff hB, ← Nat.cast_inj (R := ℚ)]
  push_cast
  rfl

theorem hookLengthSquare_lt_three (k : ℕ) (hk : k < 3) :
    (gSYT k : ℚ) = ((k * k) ! : ℕ) * ksConst k := by
  rw [hookLengthSquare_iff]
  revert k
  decide

end RMT
