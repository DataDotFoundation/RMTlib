import RMTlib

/-!
# RMTlib read through the places frame (`MeaningLib.Frame.places`)

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
