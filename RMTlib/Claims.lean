import MeaningLib.Claim
import RMTlib.BDTW.PatternA
import RMTlib.Symmetric.Wall
import RMTlib.Fock.SchurPowerSum
import RMTlib.Fermion.Transport
import RMTlib.Places.StringInsertion
import RMTlib.Places.HookValuation
import RMTlib.Symmetric.Specialise
import RMTlib.Edges.WallBreaking

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

/-- **J2**: ω is the same particle–hole swap at ∞ and at every prime. Proved at ∞ (the Maya diagram
of `λ′` is the conjugate of that of `λ`); at a prime only checked (#53: core statistics). -/
def omegaEveryPlace : Claim where
  text := "ω acts as the same particle–hole swap at ∞ (on Maya diagrams) and at every prime \
    (on each abacus, through cores)"
  scope := .junction
  declared := .checked
  statements := [``RMT.Fermion.ofRows_transpose]
  joins := [``places, ``bosonFermion]
  source := "RMTlib#53: 271 and 3,348 exact checks; the ∞ half is RMT.Fermion.ofRows_transpose"

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

end RMT.Claims
