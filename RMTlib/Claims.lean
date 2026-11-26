import MeaningLib.Claim
import RMTlib.BDTW.PatternA
import RMTlib.Symmetric.Wall
import RMTlib.Fock.SchurPowerSum
import RMTlib.Fermion.Transport
import RMTlib.Places.StringInsertion
import RMTlib.Places.HookValuation
import RMTlib.Symmetric.Specialise
import RMTlib.Edges.WallBreaking
import RMTlib.Places.BandStep
import RMTlib.Places.Tower
import RMTlib.Places.TowerPlaces
import RMTlib.Tableaux.MultisetHook.CoreCount
import RMTlib.RSK.GrowthNull

/-!
# RMTlib's claims (RMTlib#56)

RMTlib owns the **places** and **boson–fermion** hedgehogs, their junction, and the duty to
communicate them (programme owner's decision, RMTlib#56; MeaningLib#45). Each claim is stated as
data, with the Lean statements that realise it. `#claim_report in RMT.Claims` checks every claim
against the corpus and prints the sentence a note or video may use (its `say:` line). Notes and
videos quote that sentence, never more. `docs/claims.md` is the readable version of this file.
-/

namespace RMT.Claims

open MeaningLib.Claim

/-! ## Hedgehogs -/

/-- **H1, places** (our reading of Scholze's programme, not a claim of Scholze's). -/
def places : Claim where
  text := "every place, ∞ included, is one kind of object, and a statement at one place has a \
    counterpart at the others that moves the content, the support (the wall) or the one-body potential"
  scope := .hedgehog
  declared := .conjecture
  source := "RMT.Frames.places (hosted in RMTlib since #58)"

/-- **H2, boson–fermion**: classical; RMTlib proves pieces of it (see `mayaTranspose`). -/
def bosonFermion : Claim where
  text := "Schur functions correspond to fermionic states on Maya diagrams, with ω acting as \
    particle–hole conjugation"
  scope := .hedgehog
  declared := .published
  source := "classical (vertex operators, the infinite wedge)"

/-! ## Junctions -/

/-- **J1**: the place enters through a one-body potential, proved for BDTW pattern A. -/
def onebodyPotential : Claim where
  text := "for BDTW pattern A, the place enters only through a one-body weight on Maya sites, \
    which is exponential-linear at a finite place and not at ∞"
  scope := .junction
  declared := .proved
  statements := [``RMT.BDTW.det_mul_diagonal_mul_transpose, ``RMT.BDTW.isExpLinear_rhoFin,
    ``RMT.BDTW.not_isExpLinear_rhoInf]
  joins := [``places, ``bosonFermion]
  pin := some "RMTlibExamples/Frames.lean: bdtw_inf instance and witness; REFUTED potential row"

/-- **J2**: ω is the same particle–hole swap at ∞ and at every prime. At ∞ the Maya diagram of `λ′`
is the conjugate of that of `λ`; on each `r`-abacus transposition reverses the runners, negates their
charges and conjugates the quotient, so `core_r(λ′) = core_r(λ)′`; and the `p`-adic part of the hook
product is a core statistic (#53 item 2). -/
def omegaEveryPlace : Claim where
  text := "ω acts as the same particle–hole swap at ∞ (on Maya diagrams) and at every prime \
    (on each abacus, through cores)"
  scope := .junction
  declared := .proved
  statements := [``RMT.Fermion.ofRows_transpose, ``RMT.MultisetHook.quot_transpose,
    ``RMT.MultisetHook.core_transpose, ``RMT.MultisetHook.card_hooks_dvd,
    ``RMT.MultisetHook.padicValNat_prod_hooks]
  joins := [``places, ``bosonFermion]
  source := "RMTlib#53, #1 §3; the 271 and 3,348 exact checks that preceded the proofs \
    (scripts/hook_places_check.py)"
  evidence := ["evidence/hook_places_check.evidence.json"]

/-! ## Foxes -/

/-- **F1**: the boson's wall, proved through the fermion's. -/
def wallThroughPauli : Claim where
  text := "a Schur polynomial in m variables vanishes on shapes with more than m rows, as the \
    ω-image of e_k = 0 for k > m"
  scope := .fox
  declared := .proved
  statements := [``RMT.Symmetric.schurV_eq_zero_of_length]
  supports := [``bosonFermion]

/-- **F2**: `L₁` removes one box with weight `a + c`, in the power-sum model, at every charge. -/
def l1RemovesBox : Claim where
  text := "L₁ at charge a removes one box from a Schur function with weight a + c"
  scope := .fox
  declared := .proved
  statements := [``RMT.Fock.Virasoro.L1_eDetP, ``RMT.Fock.Virasoro.L1_eP]

/-- **H2's proved piece**: the Maya diagram of `λ′` is the particle–hole conjugate of `λ`'s. -/
def mayaTranspose : Claim where
  text := "the Maya diagram of the rows of λ′ is the particle–hole conjugate of that of λ"
  scope := .fox
  declared := .proved
  statements := [``RMT.Fermion.ofRows_transpose, ``RMT.Fermion.occ_ofRows_rowLen]
  supports := [``bosonFermion]

/-- **F3**: the string-insertion identity. -/
def stringInsertionIdentity : Claim where
  text := "inserting a string S into a Maya set L multiplies the Vandermonde by that of S and by \
    the mutual energy of L and S"
  scope := .fox
  declared := .proved
  statements := [``RMT.StringInsertion.vd_union, ``RMT.StringInsertion.fac_union]

/-- **F4**: the string-insertion law along theta lifts. Checked exhaustively on all admissible
Harish-Chandra parameter sets in two small windows (RH-Dual #48: 23,744 and 1,268,736 cases), with no
exception and no family cancellation. In the exact split `Δ log H = T + S + V`, the one-body share
`T/Δ` overshoots 1 and decays with `t` (1.117 at `t = 3`, 1.046 at `t = 17`, matching the worked
example), and the Vandermonde share decays (RH-Dual #54). Not in Lean, so it stays `checked`. -/
def stringInsertionLaw : Claim where
  text := "along the theta lifts, the slack changes by one-body plus two-body increments of \
    inserted strings, telescopes, and has commuting squares"
  scope := .fox
  declared := .checked
  source := "RH-Dual #48, bridge/scripts/slack_family.py (exhaustive on (k,m,t) = (3,2,3), (4,3,3)); \
    RH-Dual #39 (worked example); docs/string-insertion.md"

/-- **F6**: hook products at every place. -/
def hookEveryPlace : Claim where
  text := "H(λ) divides |λ|!, and v_p H(λ) + v_p f^λ = v_p |λ|! at every prime"
  scope := .fox
  declared := .proved
  statements := [``RMT.hookProd_dvd_factorial, ``RMT.padicValNat_hookProd_add_fSYT]
  supports := [``places]

/-- **F7, Rankin–Selberg by rows**: at a split prime the Mellin step of the unfolding (the one-row
Dirichlet series) and the full Cauchy kernel differ exactly by the second row, the factor
`1 − x y x′ y′ c² X²` (the Eisenstein series' `ζ(2s)`). Both forms occur in the proof, in different
nodes (RH-Dual #66: the `GL_a` unfolding uses the full kernel; the `GL₂` Hecke node the one-row
series). -/
def rankinSelbergRows : Claim where
  text := "at a split prime, the one-row Rankin–Selberg series times the full Cauchy kernel's \
    inverse is exactly the second-row factor 1 − x y x' y' c² X², and the full kernel sums all shapes"
  scope := .fox
  declared := .proved
  statements := [``RMT.Symmetric.oneRow_cauchy_two, ``RMT.Symmetric.cauchy_powerSeries]
  supports := [``places]
  source := "RH-Dual #66 (both forms in the proof, in different nodes)"

/-- **F8**: one wall breaks `ω`, two walls restore it. Behind the boson's wall an `ω`-odd statistic
(`λ₁ − ℓ(λ)`, odd content moments) is biased, and the bias is carried exactly by the shapes that
cross the fermion's wall; on the box it vanishes again. -/
def wallBreaksOmega : Claim where
  text := "behind one wall (ℓ(λ) ≤ N) an ω-odd statistic is carried exactly by the shapes with \
    λ₁ > N; with no wall, or two walls (the N × N box), its weighted sum is zero"
  scope := .fox
  declared := .proved
  statements := [``RMT.Edges.sum_bosonWall_odd, ``RMT.Edges.sum_box_odd_eq_zero,
    ``RMT.Edges.sum_bosonWall_transpose, ``RMT.Edges.sum_odd_eq_zero,
    ``RMT.Edges.two_mul_sum_odd_eq_sum_defect]
  supports := [``bosonFermion]

/-- **F9**: one lift is one step. Translating a Maya set by `Δ` and inserting the crossing charge
`ℓ` changes `log H` by exactly `T + S + V` (RMTlib#72): the exact split RH-Dual computed (F4). -/
def bandStep : Claim where
  text := "Δ log H = T + S + V for translate-then-insert on any finite Maya set: T the translation, \
    S = log ℓ! the self-energy, V = −Σ log|x + Δ − ℓ| the Vandermonde; on the hole side \
    (remove the lowest hole, translate down by Δ ≥ 1) H never increases"
  scope := .fox
  declared := .proved
  statements := [``RMT.StringInsertion.log_hset_step, ``RMT.StringInsertion.hset_step,
    ``RMT.StringInsertion.vd_shift, ``RMT.StringInsertion.hset_drain]
  supports := [``places]

/-- **F10**: the theta tower at one place is one object (RMTlib#79). Read through the band, each
level is the cut `(a⁺_i, a⁻_i)` of one configuration; with the band empty and one crossing per lift,
the particle side obeys F9's step law, the hole side drains, the charge is conserved, and the
reflection `X ↦ −X` swaps the sides and keeps the factor at `∞`. -/
def towerOneObject : Claim where
  text := "the theta tower at a place is one configuration read through a band: per lift, \
    a⁺ gains the crossing point (Δ log H = T + S + V), a⁻ loses it and H(a⁻) drains, \
    |a⁺| + |a⁻| = |X|, and X ↦ −X swaps a⁺ and a⁻; at every prime the step has the same split, \
    and log H is the sum of its p-adic readings"
  scope := .fox
  declared := .proved
  statements := [``RMT.Tower.cut_succ_fst, ``RMT.Tower.cut_fst_snd,
    ``RMT.Tower.log_hset_above_succ, ``RMT.Tower.hset_below_succ_le, ``RMT.Tower.hset_above_le_succ, ``RMT.Tower.card_cut,
    ``RMT.Tower.cut_reflectTower, ``RMT.Tower.factorInf_reflectTower,
    ``RMT.Tower.padicValRat_above_succ, ``RMT.Tower.log_factorInf_eq_sum, ``RMT.Tower.vdZ_level, ``RMT.Tower.log_hset_above_succ_succ, ``RMT.Tower.hset_cut_narrow,
    ``RMT.StringInsertion.log_hset_step_gap, ``RMT.StringInsertion.log_hset_step_gap_mono,
    ``RMT.StringInsertion.log_hset_step_gap_V_le, ``RMT.StringInsertion.translation_le_step]
  supports := [``places, ``bosonFermion]

/-- **F11**: Alpöge's proof uses `ω` (`λ ↦ λ′`) as a duality at **no** place. No Aubert /
Zelevinsky involution, no Alvis–Curtis, no Iwahori–Matsumoto at the finite places; at `∞` the Fock
model is bosonic only and `YoungDiagram.transpose` is never called. The dualities the proof uses
are contragredients (`ν ↦ ν⁻¹` at `p`, `−w₀` at `∞`): on Maya diagrams the band's `a⁻` reflection
(`RMT.Tower.reflectTower`), which is `ω` *without* the particle–hole complement. Column data of
shapes is used, but never to prove a statement about `λ′` from one about `λ`. (Corrected: an earlier
version said "at `∞` only"; RH-Dual #101.) -/
def omegaAtNoPlace : Claim where
  text := "the proof uses ω (λ ↦ λ′) as a duality at no place; its dualities are contragredients, \
    which on Maya diagrams are the reflection without the particle–hole complement"
  scope := .fox
  declared := .checked
  source := "RH-Dual #89, #95, #101: bridge/links/omega-finite-places.md, \
    bridge/links/omega-infinite-places.md, bridge/scripts/closure_names.py"
  supports := [``bosonFermion, ``places]

/-- **F12**: the proof is bosonic throughout. Every partition sum it truncates sits behind the
boson wall at the rank (none behind a fermion wall), the `ω`-images of its sums (dual Cauchy,
vertical-strip Pieri) are absent from its closure, and its kernel positivities fail under the
fermionic twin (the Jacquet–Shalika log-coefficients become `(−1)^{k+1}|p_k|²/k`, negative at
`k = 2`). Together with F11 this locates `ω`'s role exactly: it is absent from the proof, and the
proof's positivity is what it would break. -/
def bosonicProof : Claim where
  text := "every wall sum in the proof is behind the boson wall at the rank, the ω-images of its \
    sums are absent, and its kernel positivities fail under the fermionic twin"
  scope := .fox
  declared := .checked
  source := "RH-Dual #86, #92, #98: bridge/links/wall-sums.md, bridge/links/positivity-census.md, \
    bridge/scripts/wall_positivity_census.py (twins checked exactly)"
  supports := [``bosonFermion]

/-- **F13**: the proof's vacuum character splits as **point ⊗ charge** (RMTlib#83's roles). The
character `mu = χV(x)` (`x` a Hilbert-90 root of `det g`) is one global character, the same at
every place (point). At `∞` the proof's `muInf = mu_∞ · j` carries an extra frame factor
`j = ∏ det(k₊)^m det(k₋)^{−m}`, `m = rk V / 2`, fixed by the signature and rank (charge); at the
finite places the charge is absent. `ω` (`m ↦ −m`) inverts `j` and fixes `mu`: its asymmetry is
purely in the archimedean charge. -/
def vacuumPointCharge : Claim where
  text := "the vacuum character is a place-uniform point (mu) times an archimedean charge factor \
    (j, from the signature); ω inverts the charge and fixes the point"
  scope := .fox
  declared := .checked
  source := "RH-Dual #7, #122, #125: bridge/links/vacuum-character-places.md (read); \
    the factorisation muInf = mu_∞ · j proved in RH-Dual's Lean, lane C, RH-Dual #138"
  supports := [``places, ``bosonFermion]

/-- **F14**: the place enters a content weight as **point × charge**,
`T^{|λ|} · ∏ (N + c)` (`contentProd_point_charge`), one argument for `∞` and for the charged finite
places; the uncharged Euler factor is a limit of it, not an instance (RH-Dual #132:
`tendsto_rescaled_content`). On the proof's `LocalDatum` twins: charge 4/4, point 1/2, topology 0/3
(transport blocked at summation). -/
def pointChargeFactorisation : Claim where
  text := "a place's content weight is point^|λ| times the charge's content product; at ∞ only the \
    charge acts, at an unramified place only the point (as a limit)"
  scope := .fox
  declared := .proved
  statements := [``RMT.Symmetric.contentProd_point_charge, ``RMT.Symmetric.contentProd_const]
  supports := [``places]

/-! ## The null chart (RMTlib#154): squares and grids -/

/-- **Fomin's local rule as a square** (RMTlib#154): inputs on the west and south edges (the
neighbours `μ`, `ν` and the corner `ρ`), output on the east and north. It is a function of its
inputs (`fwd`), and invertible on every square that occurs (`bwd_fwd`). -/
def fominSquare : Claim where
  text := "Fomin's local rule: the shape at the north-east corner is a function of the other three \
    and the entry, and the backward rule recovers them"
  scope := .fox
  declared := .proved
  statements := [``RMT.RSK.Growth.bwd_fwd]
  square := some ("shape", "shape", "shape", "shape")
  determined := true

/-- **RSK's growth diagram as a discrete Goursat problem** (RMTlib#154 target 1): the grid of
Fomin squares is determined by its two outer (null) edges, through the local rule. -/
def growthGoursat : Claim where
  text := "a growth diagram is determined by its two outer edges: the backward grid rebuilds every \
    shape and every entry from them (RSK as a discrete Goursat problem)"
  scope := .fox
  declared := .proved
  statements := [``RMT.RSK.Growth.back_grow]
  square := some ("shape", "shape", "shape", "shape")
  tiles := [[``fominSquare, ``fominSquare], [``fominSquare, ``fominSquare]]
  determined := true

end RMT.Claims
