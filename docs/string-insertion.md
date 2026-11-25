# The string-insertion law (a hypothesis about slack, stated in RMTlib's vocabulary)

RMTlib#49 (from RH-Dual, at the user's direction). This note states the hypothesis without reference
to Alpöge's proof, separates what is **exact** from what is **conjectural**, and says what would
refute it. Tags: **proved** (in RMTlib), **exact** (elementary, to be formalised: RMTlib#49 Ask 2),
**conjecture**.

## Objects

- A **Maya set** `L ⊂ ℕ` is a finite set of occupied sites. A partition `λ` with at most `N` rows gives
  `L(λ) = {λ_i + N − 1 − i : i < N}` (`RMT.Fermion`, `occ_ofRows_rowLen` up to the shift by the charge).
- The **set hook product**
  `Hset(L) = ∏_{ℓ ∈ L} ℓ! / ∏_{ℓ < ℓ′ ∈ L} (ℓ′ − ℓ)`.
  By Frobenius (`RMT.frobenius`, proved), `Hset(L(λ)) = H(λ)`, the hook product, independently of the
  padding `N`.
- A **string** is a set `S = {a, a + 1, …, a + t − 1}` of consecutive sites; it is **insertable** in `L`
  if `S ∩ L = ∅`.
- The **mutual energy** of disjoint sets is `Mut(L, S) = ∏_{ℓ ∈ L, s ∈ S} |ℓ − s|`.

## The exact part

1. **Insertion identity** (exact): for disjoint `L`, `S`,
   `Hset(L ⊔ S) · Mut(L, S) = Hset(L) · Hset(S)`.
   The increment of `log H` on inserting `S` is `log Hset(S) − log Mut(L, S)`: a **self-energy** of the
   string minus its **mutual energy** with what is already there. For a string, `Hset(S)` is
   explicit: `∏_{s ∈ S} s! / ∏_{k < t} k!` (the Vandermonde of consecutive integers is superfactorial).
2. **Telescoping** (exact): for disjoint strings inserted in sequence, the total quotient is the product
   of the increments, each taken against everything inserted before.
3. **Square rule** (exact): two disjoint strings inserted in either order give the same set, hence equal
   products. At the level of sets, the commuting square has **no defect**.
4. **Place reading** (exact): `Hset(L) = ∏_{ℓ ∈ L} ρ_∞(ℓ) / Δ(L)`, where `ρ_∞(ℓ) = ℓ!` is the one-body
   weight at ∞ (`RMT.BDTW.rhoInf`) and `Δ` the Vandermonde. With `ρ_p(ℓ) = T^ℓ` instead
   (`RMT.BDTW.rhoFin`) the self-energy of a string is `T^{Σ S}`, **affine** in its position. So a string's
   self-energy depends on where it sits only through the non-affine part of `log ρ_∞`
   (`¬ IsExpLinear rhoInf`, proved), and the mutual energy `Mut` is place-uniform. This is
   RMTlib#21's root (b) at the level of slack.

## The hypothesis

**String-insertion law (conjecture).** Along the theta lifts of a proof (RH-Dual's tower grid and
lower-bound lifts), each step acts on the relevant Maya sets as **insertion of a string**, possibly
combined with a **translation** `L ↦ L + Δ`. Two different things are easily confused here:
- **re-padding** (`N ↦ N + 1`: add a particle at `0` and shift the rest by `1`) is a **gauge**: it leaves
  `Hset` unchanged (exact; e.g. `Hset{0,2,5} = Hset{0,1,3,6} = 8`);
- a plain **translation is not a gauge**: it changes every `ℓ!` (`Hset{1,3,6} = 144`). Its effect is the
  one-body factor `Hset(L + Δ)/Hset(L) = ∏_{ℓ ∈ L} (ℓ + 1)_Δ` (rising Pochhammer; the Vandermonde is
  translation-invariant), i.e. the `log Γ` potential of item 4 transported by `Δ`. RH-Dual's first data
  on the proof's lower-bound lifts (#49) show exactly this: one charge migrating plus a translation,
  with about 95 % of `Δ log H` one-body.

In consequence:
- (a) the **slack** (RH-Dual's gauge-free statistic, for example `Σ log H(a⁻)` at node 18 or `log f^λ` at
  node 4) changes at each step by the exact increment of item 1;
- (b) it **telescopes** along any path (item 2);
- (c) the grid of lifts is a **growth diagram** whose squares commute exactly (item 3). A measured
  defect therefore locates a step that is **not** a disjoint string insertion, e.g. a collision
  (`S ∩ L ≠ ∅`, a Pauli obstruction) or a translation not accounted for by its Pochhammer factor;
- (d) asymptotically, the total slack is a **log-gas energy**: one-body `Σ log ℓ!` minus two-body
  `Σ log |ℓ − ℓ′|`. This is consistent with the `k² log k` growth at the square (RMTlib's Keating–Snaith
  constant, `ksConst_eq_inv_mutual`, is already a mutual energy of two adjacent strings).

## What would refute it

- A lift step whose shapes are not related by a disjoint string insertion, up to re-padding and a
  translation (with its Pochhammer factor). The
  hypothesis is falsified there, and the defect of (c) should be nonzero exactly at such steps.
- A gauge-free slack increment that differs from `log Hset(S) − log Mut(L, S)` at a step that *is* a
  string insertion.
- Commuting squares with a nonzero defect while both routes are disjoint insertions. That cannot
  happen if items 1–3 are right, so it would point to a mis-identified Maya set.

## Status and next steps

- Items 1–3 at the set level: to be formalised in RMTlib (RMTlib#49 Ask 2), with the valuation
  package of RMTlib#41 applied to `Hset`, so that slack is homogeneous at every place.
- RH-Dual tests (a)–(c) on the proof's grid (`k = 8, m = 4, t = 17`), with predictions committed first.
- The `f^λ` and content-product versions (Ask 2.2) follow from `f^λ = |λ|!/H(λ)` and
  `∏(N + c) = ∏ ℓ!/∏ (N − 1 − i)!` at the same Maya positions.
