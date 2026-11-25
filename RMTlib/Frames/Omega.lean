import RMTlib.Frames.InvolutionLaws
import RMTlib.Symmetric.OmegaCovariantInstances
import RMTlib.Symmetric.DualJacobiTrudi
import RMTlib.Fock.Virasoro
import RMTlib.Fock.DehayeDelta
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# RMTlib's spec for `ω` (the ω-twin finder)

`ω` is transposition of shapes, `μ ↦ μ′`: `YoungDiagram.transpose`, and `RMT.Symmetric.conjV` on
padded shapes. Its operator form acts on `Λ` and `Λ₂` (`RMT.Fock.Virasoro.omega`,
`RMT.Fock.DehayeDelta.omega2`, `omegaL`). Matrix transposition is a different involution. Laws are
recorded by `RMT.Symmetric.OmegaCovariant`.

Run `#involution_laws RMT.Frames.omegaSpec in RMT` (`RMTlibExamples/Omega.lean` pins it).
-/

namespace RMT.Frames

/-- The spec of `ω` in RMTlib. -/
def omegaSpec : Involution.Spec where
  name := "ω"
  shapes := [``YoungDiagram.transpose, ``RMT.Symmetric.conjV]
  operators := [``RMT.Fock.Virasoro.omega, ``RMT.Fock.DehayeDelta.omega2,
    ``RMT.Fock.DehayeDelta.omegaL]
  others := [``Matrix.transpose]
  recorder := some ``RMT.Symmetric.OmegaCovariant
  nameHints := ["transpose", "conj", "omega", "swap"]

end RMT.Frames
