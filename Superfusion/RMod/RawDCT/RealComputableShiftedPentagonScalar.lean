import Superfusion.RMod.RawDCT.RealComputableShift
import Superfusion.RMod.RawDCT.RealPChiAllCoordinates
import Superfusion.RMod.RawDCT.ShiftPentagonScalar

/-!
# Every-coordinate scalar cancellation for the computable real shift

The actual unshifted route bridge identifies every top coordinate with the
computable `chi` value times the corresponding bottom coordinate.  The
generic `(nu, beta)` ledger then cancels that value without recomputing any
fourfold route.

This file records the resulting equality of the two shifted route scalar
expressions at every stored source/target coordinate.  Full typed route
coherence is supplied separately by
`RealComputableShiftedConnectorSemantic.lean`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open RealPChiKernel

/-! ## All-coordinate cancellation -/

/-- The top scalar times the actual raw top coefficient equals the bottom
scalar times the actual raw bottom coefficient at every coordinate. -/
theorem realComputableShifted_scalarCoordinate_eq
    (a b c d : ZMod 8)
    (source : QuadSource a b c d) (target : QuadTarget a b c d) :
    (shiftPentagonTopScalar realRawDCT.data realComputableNuBeta.data
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) : ℝ) *
          ((topCoeff a b c d source target : ℤ) : ℝ) =
      (shiftPentagonBottomScalar realComputableNuBeta.data
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) : ℝ) *
          ((botCoeff a b c d source target : ℤ) : ℝ) := by
  apply shiftPentagonScalar_eq_of_sourceDefect_bundled
    realRawDCT realComputablePChi realComputableNuBeta
  exact RealPChiAllCoordinates.cast_topCoeff_eq_tableValue_mul_cast_botCoeff
    a b c d source target

/-! ## Nontrivial sectors -/

example (source : QuadSource 4 4 4 4) (target : QuadTarget 4 4 4 4) :
    (shiftPentagonTopScalar realRawDCT.data realComputableNuBeta.data
        (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4)
        (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4) : ℝ) *
          ((topCoeff 4 4 4 4 source target : ℤ) : ℝ) =
      (shiftPentagonBottomScalar realComputableNuBeta.data
        (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4)
        (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4) : ℝ) *
          ((botCoeff 4 4 4 4 source target : ℤ) : ℝ) :=
  realComputableShifted_scalarCoordinate_eq 4 4 4 4 source target

example (source : QuadSource 5 5 5 5) (target : QuadTarget 5 5 5 5) :
    (shiftPentagonTopScalar realRawDCT.data realComputableNuBeta.data
        (Multiplicative.ofAdd 5) (Multiplicative.ofAdd 5)
        (Multiplicative.ofAdd 5) (Multiplicative.ofAdd 5) : ℝ) *
          ((topCoeff 5 5 5 5 source target : ℤ) : ℝ) =
      (shiftPentagonBottomScalar realComputableNuBeta.data
        (Multiplicative.ofAdd 5) (Multiplicative.ofAdd 5)
        (Multiplicative.ofAdd 5) (Multiplicative.ofAdd 5) : ℝ) *
          ((botCoeff 5 5 5 5 source target : ℤ) : ℝ) :=
  realComputableShifted_scalarCoordinate_eq 5 5 5 5 source target

end Superfusion.RMod.RawDCT
