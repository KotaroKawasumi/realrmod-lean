import Superfusion.RMod.RawDCT.PChiShift
import Superfusion.RMod.RawDCT.RealComputableNuBeta

/-!
# Computable real raw shift

This concrete instance specializes the generic raw `(nu, beta)` shift to the
executable real tables.  Data, laws, and completed bundles are constructed in
that order.  The shifted connector parity is pointwise zero and its formally
transported scalar obstruction is pointwise one, by the generic cochain
cancellation theorems.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Shift data, laws, and completed raw DCT -/

/-- The source-indexed computational shift data. -/
def realComputableShiftData : ShiftData realRawDCTData :=
  ShiftData.ofNuBetaData realRawDCTData realComputableNuBeta.data

/-- Generic preservation laws specialized to the exact computable data. -/
def realComputableShiftLaws :
    ShiftLaws realRawDCTData realRawDCTLaws realComputableShiftData :=
  shiftLawsOfNuBetaData realRawDCTData realRawDCTLaws
    realComputableNuBeta.data

/-- The completed computable shift prescription. -/
def realComputableShift : Shift realRawDCT where
  data := realComputableShiftData
  laws := realComputableShiftLaws

/-- The completed computable raw DCT after regrading and connector
rescaling. -/
def realComputableShiftedRawDCT : RawDCT :=
  realComputableShift.shifted

/-! ## Shifted obstruction data, laws, and completed package -/

/-- The computationally transported scalar obstruction. -/
def realComputableShiftedPChiData : PChiData :=
  shiftPChiData realRawDCTData realComputablePChi.data
    realComputableNuBeta.data

/-- Gu--Wen laws for that exact shifted data. -/
def realComputableShiftedPChiLaws :
    PChiLaws realComputableShiftedRawDCT.data
      realComputableShiftedRawDCT.laws realComputableShiftedPChiData :=
  shiftPChiLaws realRawDCTData realRawDCTLaws
    realComputablePChi.data realComputablePChi.laws
    realComputableNuBeta.data realComputableNuBeta.laws
    realComputableShiftedRawDCT.laws

/-- The completed shifted obstruction package. -/
def realComputableShiftedPChi :
    PChi realComputableShiftedRawDCT where
  data := realComputableShiftedPChiData
  laws := realComputableShiftedPChiLaws

/-! ## Pointwise triviality -/

/-- Regrading by the computable `nu` makes the stored connector parity
pointwise even. -/
theorem realComputableShiftedRawDCT_parity_eq_zero
    (a b c : RawDCTGroup) :
    rawParity realComputableShiftedRawDCT.data a b c = 0 :=
  rawParity_shiftRawDCTData_eq_zero
    realRawDCTData realRawDCTLaws
    realComputablePChi.data realComputablePChi.laws
    realComputableNuBeta.data realComputableNuBeta.laws a b c

/-- Rescaling by the computable `beta` makes the transported scalar
obstruction pointwise one. -/
theorem realComputableShiftedPChi_chi_eq_one
    (a b c d : RawDCTGroup) :
    realComputableShiftedPChi.data.chi a b c d = 1 :=
  shiftPChiData_chi_eq_one
    realRawDCTData realRawDCTLaws
    realComputablePChi.data realComputablePChi.laws
    realComputableNuBeta.data realComputableNuBeta.laws a b c d

/-! ## Closed nontrivial examples -/

/-- The original odd sector becomes even after the executable shift. -/
example :
    rawParity realRawDCT.data
        (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1)
        (Multiplicative.ofAdd 4) = 1 ∧
      rawParity realComputableShiftedRawDCT.data
        (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1)
        (Multiplicative.ofAdd 4) = 0 := by
  constructor
  · exact realRawDCT_example_parity
  · exact realComputableShiftedRawDCT_parity_eq_zero _ _ _

/-- The completed shift genuinely contains the nonzero binary regrading at
`(1,1)`. -/
example :
    realComputableShift.data.nu
      (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1) = 1 :=
  rfl

end Superfusion.RMod.RawDCT
