import RMTlib

/-!
# RMTlib read through the places frame (`RMT.Frames.places`)

Loop 1 (`docs/loops/`). Pins the report on the restated moment polynomial and Theorem 3: each is
read (it mentions `archContent`), and the frame proposes its finite-place twin, with no witness.
Both proposals are false: `RMT.UN.twinPoly_coeff_two_ne`, `RMT.UN.not_theorem3_and_twin_two_two`.
The report decides nothing about truth.
-/

/--
info: frame places, binding RMT.Frames.placesBinding, on RMT.UN.momentPoly_eq_contentProd: 1 theorems, 1 read, 0 unread
RMT.UN.momentPoly_eq_contentProd: reads [archContent]
  twin archContent ↦ finContent: proposed
    ∀ (k : ℕ),
      RMT.UN.momentPoly k =
        Polynomial.C (RMT.UN.weights k).prod⁻¹ *
          RMT.Symmetric.contentProd (RMT.Frames.finContent (Polynomial.X + Polynomial.C ↑k)) (RMT.UN.square k)
-/
#guard_msgs (whitespace := lax) in
#frame_report RMT.Frames.placesBinding in RMT.UN.momentPoly_eq_contentProd

/-! RMTlib as a checker (RMTlib#7, MeaningLib#11): the statements tagged `@[frame_pattern]`. -/

open Lean Elab Command in
/--
info: 28 patterns: [RMT.hookProd_dvd_factorial,
 RMT.hook_content_formula,
 RMT.padicValNat_hookProd,
 RMT.padicValNat_hookProd_add_fSYT,
 RMT.BDTW.det_mul_diagonal_mul_transpose,
 RMT.Fock.fischer_X_mul_le,
 RMT.Fock.fischer_eX_contentProd,
 RMT.Fock.fischer_hX_contentProd,
 RMT.Fock.fischer_hX_eq_neg_eX,
 RMT.Fock.fischer_pderiv_le,
 RMT.Plethysm.sum_sq_eq,
 RMT.Plethysm.sum_sq_eq_hTwo_add,
 RMT.Plethysm.sum_sq_eq_hTwo_sub,
 RMT.Positivity.det_mul_transpose_eq_sum_sq,
 RMT.Positivity.trace_sq_le_card_mul_trace_mul_self,
 RMT.StringInsertion.vd_union,
 RMT.Symmetric.cauchy_hasSum,
 RMT.Symmetric.cauchy_inf,
 RMT.Symmetric.cauchy_powerSeries,
 RMT.Symmetric.cauchy_prod,
 RMT.Symmetric.cauchy_weighted,
 RMT.Symmetric.dual_cauchy,
 RMT.Symmetric.dual_cauchy_one,
 RMT.Symmetric.hE_eq_sum_sym,
 RMT.Symmetric.oneRow_cauchy_two,
 RMT.Symmetric.schurV_conjV_eq_eDet,
 RMT.Symmetric.schurV_eq_det,
 RMT.Symmetric.schurV_eq_eDet_conjV]
-/
#guard_msgs (whitespace := lax) in
run_cmd do
  let ps := MeaningLib.Frame.framePatterns (← getEnv) "places"
  logInfo m!"{ps.size} patterns: {ps.toList}"

/-! The theta checker (RMTlib#7 item 1). Unnamed patterns belong to every frame; `ker_intertwine` (a
change of model that intertwines the actions and matches the read-outs gives equal kernels) belongs
to `theta` only. -/

open Lean Elab Command in
/--
info: 29 patterns: [RMT.hookProd_dvd_factorial,
 RMT.hook_content_formula,
 RMT.padicValNat_hookProd,
 RMT.padicValNat_hookProd_add_fSYT,
 RMT.BDTW.det_mul_diagonal_mul_transpose,
 RMT.Fock.fischer_X_mul_le,
 RMT.Fock.fischer_eX_contentProd,
 RMT.Fock.fischer_hX_contentProd,
 RMT.Fock.fischer_hX_eq_neg_eX,
 RMT.Fock.fischer_pderiv_le,
 RMT.Plethysm.sum_sq_eq,
 RMT.Plethysm.sum_sq_eq_hTwo_add,
 RMT.Plethysm.sum_sq_eq_hTwo_sub,
 RMT.Positivity.det_mul_transpose_eq_sum_sq,
 RMT.Positivity.trace_sq_le_card_mul_trace_mul_self,
 RMT.StringInsertion.vd_union,
 RMT.Symmetric.cauchy_hasSum,
 RMT.Symmetric.cauchy_inf,
 RMT.Symmetric.cauchy_powerSeries,
 RMT.Symmetric.cauchy_prod,
 RMT.Symmetric.cauchy_weighted,
 RMT.Symmetric.dual_cauchy,
 RMT.Symmetric.dual_cauchy_one,
 RMT.Symmetric.hE_eq_sum_sym,
 RMT.Symmetric.oneRow_cauchy_two,
 RMT.Symmetric.schurV_conjV_eq_eDet,
 RMT.Symmetric.schurV_eq_det,
 RMT.Symmetric.schurV_eq_eDet_conjV,
 RMT.Fock.ThetaKernel.ker_intertwine]
-/
#guard_msgs (whitespace := lax) in
run_cmd do
  let ps := MeaningLib.Frame.framePatterns (← getEnv) "theta"
  logInfo m!"{ps.size} patterns: {ps.toList}"

/-! The potential roles (MeaningLib#4, RMTlib#19 B7): `IsExpLinear` is the located reason. The
twin of the refutation at `∞` is refuted at a finite place; the twin of the finite fact at `∞` is
only proposed (it is true over the trivial ring, so no unconditional refutation exists). -/

/--
info: frame places, binding RMT.Frames.placesBinding, on RMT.BDTW.not_isExpLinear_rhoInf: 1 theorems, 1 read, 0 unread
RMT.BDTW.not_isExpLinear_rhoInf: reads [archPotential]
  twin archPotential ↦ finPotential: REFUTED by RMT.BDTW.isExpLinear_rhoFin
  ∀ {R : Type u_1} [inst : CommRing R] [Nontrivial R] (T : R), ¬RMT.BDTW.IsExpLinear (RMT.BDTW.rhoFin T)
-/
#guard_msgs (whitespace := lax) in
#frame_report RMT.Frames.placesBinding in RMT.BDTW.not_isExpLinear_rhoInf

/--
info: frame places, binding RMT.Frames.placesBinding, on RMT.BDTW.isExpLinear_rhoFin: 1 theorems, 1 read, 0 unread
RMT.BDTW.isExpLinear_rhoFin: reads [finPotential]
  twin finPotential ↦ archPotential: proposed
  ∀ {R : Type u_1} [inst : CommRing R] (T : R), RMT.BDTW.IsExpLinear RMT.BDTW.rhoInf
-/
#guard_msgs (whitespace := lax) in
#frame_report RMT.Frames.placesBinding in RMT.BDTW.isExpLinear_rhoFin

-- Pattern A at `∞` is an instance of pattern A, and its finite-place twin is `bdtw_fin`.
/--
info: frame places, binding RMT.Frames.placesBinding, on RMT.BDTW.bdtw_inf: 1 theorems, 1 read, 0 unread
RMT.BDTW.bdtw_inf: reads [archPotential]
  instance of RMT.BDTW.det_mul_diagonal_mul_transpose [R := R,
 N := N,
 W := Fin K,
 ρ := fun l ↦ RMT.BDTW.rhoInf ↑l,
 A := A,
 B := B]
  twin archPotential ↦ finPotential: witness RMT.BDTW.bdtw_fin
-/
#guard_msgs (whitespace := lax) in
#frame_report RMT.Frames.placesBinding in RMT.BDTW.bdtw_inf

-- The whole library through the places frame must stay within the default heartbeats
-- (RMTlib#42: generic transfer conclusions once made this time out), with its read count pinned.
#guard_msgs (drop info) in
#frame_report RMT.Frames.placesBinding in RMT expect (read := 34) (problems := 0)
