import RMTlib.RSK.GrowthSuper

/-!
# Checks for the parity-labelled local rule

Each local rule, run forwards and backwards on small squares, against values computed by
`scripts/growth_rules.py`. In particular the rule for two fermions is not the conjugate of the
bosonic rule: on `ρ = μ = ν = (1, 0)` with entry `1` it gives `(2, 0)`, as Hage's super-RSK
insertion does, where the conjugated bosonic rule would give `(1, 1)`.
-/

namespace RMT.RSK.GrowthSuper.Examples

open RMT.RSK.GrowthSuper

-- two bosons: the entry goes into row 0; what both sides added to row 0 moves to row 1
#guard fwdC false false 1 [1, 0] [1, 0] [1, 0] == [2, 0]
#guard fwdC false false 0 [0, 0] [1, 0] [1, 0] == [1, 1]
-- two fermions: the rule of Hage's super-RSK
#guard fwdC true true 1 [1, 0] [1, 0] [1, 0] == [2, 0]
#guard fwdC true true 2 [0, 0, 0] [0, 0, 0] [0, 0, 0] == [1, 1, 0]
-- mixed: entries 0 or 1
#guard fwdC false true 1 [1, 0] [1, 0] [1, 1] == [2, 1]
#guard fwdC true false 1 [1, 0] [1, 1] [1, 0] == [2, 1]

/-- Every square with `N = 3` rows, parts `≤ 3` and entry `≤ 3` satisfying the hypotheses of
`bwd_fwd`, for each of the four parity types. -/
def squares (p q : Bool) : List (Nat × List Nat × List Nat × List Nat) :=
  let vs := (List.range 4).flatMap fun a => (List.range 4).flatMap fun b =>
    (List.range 4).map fun c => [a, b, c]
  let rel : Bool → List Nat → List Nat → Bool := fun s l m =>
    (l.zip m).all fun (r, a) => r ≤ a && (!s || a ≤ r + 1)
  (List.range 4).flatMap fun x => vs.flatMap fun ρ => vs.flatMap fun μ => vs.filterMap fun ν =>
    if rel p ρ μ && rel q ρ ν && (p == q || x ≤ 1) && carryOut p q x ρ μ ν == 0 then
      some (x, ρ, μ, ν) else none

-- the backward rule undoes the forward rule on all of them
#guard [false, true].all fun p => [false, true].all fun q =>
  (squares p q).all fun (x, ρ, μ, ν) => bwdC p q μ ν (fwdC p q x ρ μ ν) == (ρ, x)

end RMT.RSK.GrowthSuper.Examples
