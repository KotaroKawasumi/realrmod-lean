import RMod.BrundanEllis.StackingReferenceCommutorData

/-! The full real-coordinate matrices are right-linear matrices over the
endpoint division algebra. The certificate below checks this identification
against the existing multiplication table, rather than assuming it of the solver. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

/-- Read the coefficient vector by applying a matrix to the unit of one row. -/
def coefficientZ (a b : ZMod 8) (M : Matrix (Index b a) (Index a b) ℤ)
    (r : FusionTable.Index b a) (s : FusionTable.Index a b) (u : ℕ) : ℤ :=
  if hu : u < realRepDim (b + a).val then
    M (r, ⟨u, hu⟩) (s, RealPChiKernel.coefficientUnitIndex (a + b))
  else 0

/-- Recover the complete real-coordinate matrix by right-linearity. -/
def rightLinearEncoding (a b : ZMod 8) (M : Matrix (Index b a) (Index a b) ℤ) :
    Matrix (Index b a) (Index a b) ℤ := fun r s =>
  RealPChiKernel.leftMulBasisCoeff (b + a).val (coefficientZ a b M r.1 s.1) s.2.val r.2.val

/-- The exchange and its inverse numerator are genuine matrices over D(a+b). -/
theorem rightLinear_encoding (a b : ZMod 8) :
    forwardZ a b = rightLinearEncoding a b (forwardZ a b) ∧
      inverseNumeratorZ a b = rightLinearEncoding b a (inverseNumeratorZ a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor
