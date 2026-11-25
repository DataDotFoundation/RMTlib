import MeaningLib.Claim
import RMTlib.BDTW.PatternA
import RMTlib.Symmetric.Wall
import RMTlib.Fock.SchurPowerSum
import RMTlib.Fermion.Transport
import RMTlib.Places.StringInsertion
import RMTlib.Places.HookValuation

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

/-- **F4**: the string-insertion law along theta lifts: one worked example only (RH-Dual #39). -/
def stringInsertionLaw : Claim where
  text := "along the theta lifts, the slack changes by one-body plus two-body increments of \
    inserted strings, telescopes, and has commuting squares"
  scope := .fox
  declared := .checked
  source := "RH-Dual #39 (one worked example); docs/string-insertion.md"

/-- **F6**: hook products at every place. -/
def hookEveryPlace : Claim where
  text := "H(λ) divides |λ|!, and v_p H(λ) + v_p f^λ = v_p |λ|! at every prime"
  scope := .fox
  declared := .proved
  statements := [``RMT.hookProd_dvd_factorial, ``RMT.padicValNat_hookProd_add_fSYT]
  supports := [``places]

end RMT.Claims
