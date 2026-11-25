import MeaningLib.Frame.Basic

/-!
# The places frame (RMTlib's hedgehog claim)

Our reading of Scholze's programme as it is used in the RMTlib / RH-Dual work: every place of `ℚ`,
`∞` included, is one kind of object, and a statement proved at one place should have its
counterpart at the others. This is **our reading, not a claim of Scholze's** (the RH-Dual
repository keeps the literature digests that support it).

Roles, in the form in which places meet in content products `∏_{□ ∈ λ} f(c(□))`:

* `archContent`: the content function at `∞`, `c ↦ N + c` (`N` the rank, or a variable standing
  for it);
* `finContent`: the content function at a finite place, `c ↦ T` (constant; `T = p^{−s}`);
* `archSupport`: the shapes the place at `∞` sees, cut off by a **wall**: `ℓ(λ) ≤ N`, where the
  bosonic content factor `∏ (N + c)` vanishes beyond it (RMTlib: `Part N`, `Fin N → ℕ`);
* `finSupport`: the shapes a finite place sees: all of them, no wall (RMTlib: `YoungDiagram`);
* `archPotential` / `finPotential`: the one-body weight `ρ_v` on Maya sites, `ρ_∞(l) = l!` and
  `ρ_p(l) = T^l` (RMTlib: `RMT.BDTW.rhoInf`, `rhoFin T`), through which identities such as
  `det (A · diag ρ · Bᵀ)` (RMTlib#19 pattern A) depend on the place. `φ_v = log ρ_v` is affine at
  `p` and not at `∞`; that is a **predicate** on the potential (`IsExpLinear`), whose refutation at
  `∞` is the located reason a pattern needing it does not apply there (MeaningLib#28), not a rule.

Twin rules move content **and** support together (MeaningLib#4, decision D4; RMTlib#13 for the
evidence), in both directions, which are not inverse to each other: going to a finite place
removes the wall, going to `∞` creates it. A zero-locus statement then has a twin in which the
support moved, rather than a twin that is false for a reason the report cannot name.

For identities, the productive twin moves the **potential alone** (RH-Dual Loop 2, MeaningLib#4):
the rules `∞ ↦ finite (potential)` and back. `rhoFin` takes `T` and `rhoInf` does not, so the
binding's adapter for `∞ ↦ finite` has an extra binder, which becomes a fresh `∀ T` in the twin.

For statements that quantify over the places at `∞` as a whole (a sum or product over them, their
number), the partner is not one finite place but a **finite set `S` of finite places** (RH-Dual
Loop 3, MeaningLib#4): the rules `∞ ↦ S` and back move `archSet` (a finite type, such as a CM
type's embeddings) and `finSet`. A typical adapter is `fun (S : Finset Pl) => {v // v ∈ S}`, whose
`S` becomes a fresh `∀ S` in the twin; the instances the statement used (`Fintype`, decidable
equality) are synthesised again for the moved type. What only `∞` has (`card = f`, an equivalence
with the CM type) then fails to move, and the report says where.

Two `∞` effects stay separate (RMTlib#13): the wall (support roles) and the dependence of the
non-zero values on the contents (the content roles; e.g. the `Σ c²` correction at `M = 2`).

A library whose types differ between the two supports binds adapters for the support moves
(`Binding.adapters`). The places themselves (completions, absolute values, the product formula)
are a separate term, not yet in MeaningLib.

**Point, charge, topology** (MeaningLib#4 §2, RH-Dual#11; provisional, RMTlib's decision as owner).
The content roles conflate two data, which these roles separate:
`archContent = (c ↦ archCharge + c)`: at `∞` the content function carries the **charge**, while
`finContent = (c ↦ finPoint)`: at a finite place it carries the **point**. So
* `archPoint` / `finPoint`: the Mellin character `|x|_v^s` at each place (RH-Dual `mellin-null.md`).
  At `p` it is the value `t_p = p^{−s}`; at `∞` it is reached as the limit `t → 1`, after the
  rescaling the identity needs (e.g. `(1 − t)^{|μ|}` in the `q`-hook formula), not by evaluating.
* `archCharge` / `finCharge`: the vacuum data. At `∞`: rank `N`, signature `(p, q)`, band width
  `t + 1` of the theta tower (RMTlib F9, `RMT.StringInsertion.hset_step`); at an unramified finite
  place the charge is absent. Its twin `N ↦ −N` is a separate **automorphism** (the boson/fermion
  twin), not a place move.
* `archTopology` / `finTopology`: connected and liquid at `∞`, totally disconnected and solid at `p`.

One rule per datum in each direction (as for the potential), so a statement that uses only one
datum gets a twin at that level. Names as proposed on MeaningLib#4, adopted by RMTlib.

These roles are not yet bound by `RMT.Frames.placesBinding`; RH-Dual binds them when it splits
`LocalDatum` (RH-Dual#11).

**Degree** (MeaningLib#68 R4). `degree` is not an `∞`/finite pair but the sum over *all* places,
each weighted by `log N(v)`: the cone tying the place-indexed readings together (RMTlib's answer on
MeaningLib#62). Its pattern is the product formula as a degree, `RMT.Places.deg_principal`, with the
truncated inequality form `degOn_principal_le`. No rule moves it.

**Home.** By the programme owner's decision (RMTlib#56, MeaningLib#45) this frame encodes a claim RMTlib
owns, so its definition lives here; MeaningLib keeps the machinery (`Frame`, `Binding`, the report) and
a toy copy for its self-tests. Changes to the roles or rules are RMTlib's to make, with the evidence.
-/

namespace RMT.Frames

open MeaningLib.Frame

/-- The places frame (content form, with supports). -/
def places : Frame where
  name := "places"
  attribution := "our reading of Scholze's programme (RMTlib / RH-Dual), not a claim of Scholze's"
  roles := [
    { name := "archContent", doc := "content function at ∞: c ↦ N + c" },
    { name := "finContent", doc := "content function at a finite place: c ↦ T" },
    { name := "archSupport", doc := "shapes seen at ∞: ℓ(λ) ≤ N (the wall)" },
    { name := "finSupport", doc := "shapes seen at a finite place: all λ (no wall)" },
    { name := "archPotential", doc := "one-body weight at ∞: l ↦ l!" },
    { name := "finPotential", doc := "one-body weight at a finite place: l ↦ T^l" },
    { name := "archSet", doc := "the places at ∞ as a finite indexed set (e.g. a CM type's embeddings)" },
    { name := "finSet", doc := "a finite set S of finite places (e.g. the level primes)" },
    { name := "archPoint", doc := "the point at ∞: the Mellin character |x|_∞^s (Γ_ℝ), reached as the \
        limit t → 1 of the finite point, not as an evaluation" },
    { name := "finPoint", doc := "the point at a finite place: t_p = p^{−s} (the Mellin character \
        |x|_p^s, Euler factor (1 − p^{−s})^{−1})" },
    { name := "archCharge", doc := "the charge at ∞: rank N, signature (p, q), band width t + 1; \
        its twin is N ↦ −N" },
    { name := "finCharge", doc := "the charge at a finite place: none (0) in the unramified case" },
    { name := "archTopology", doc := "the topology at ∞: connected; specialisation is not continuous \
        (liquid), each sum needs its own convergence argument" },
    { name := "finTopology", doc := "the topology at a finite place: totally disconnected; \
        specialisation is continuous (solid), summable iff the terms tend to 0" },
    { name := "degree", doc := "the Arakelov degree Σ_v D_v log N(v), the sum over all places with \
        ∞ included; the product formula says principal divisors have degree 0 \
        (RMT.Places.deg_principal)" }]
  twins := []
  rules := [
    { name := "∞ ↦ finite", moves := [("archContent", "finContent"), ("archSupport", "finSupport")] },
    { name := "finite ↦ ∞", moves := [("finContent", "archContent"), ("finSupport", "archSupport")] },
    { name := "∞ ↦ finite (potential)", moves := [("archPotential", "finPotential")] },
    { name := "finite ↦ ∞ (potential)", moves := [("finPotential", "archPotential")] },
    { name := "∞ ↦ S", moves := [("archSet", "finSet")] },
    { name := "S ↦ ∞", moves := [("finSet", "archSet")] },
    { name := "∞ ↦ finite (point)", moves := [("archPoint", "finPoint")] },
    { name := "finite ↦ ∞ (point)", moves := [("finPoint", "archPoint")] },
    { name := "∞ ↦ finite (charge)", moves := [("archCharge", "finCharge")] },
    { name := "finite ↦ ∞ (charge)", moves := [("finCharge", "archCharge")] },
    { name := "∞ ↦ finite (topology)", moves := [("archTopology", "finTopology")] },
    { name := "finite ↦ ∞ (topology)", moves := [("finTopology", "archTopology")] }]

end RMT.Frames
