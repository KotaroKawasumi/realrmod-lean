import RMod.BrundanEllis.StackingReferenceCommutorData

/-! Integer coordinates of the actual reference associator. The stored raw
connector is conjugated by the two prescribed shift frames. Its remaining
scalar is the inverse of the existing beta cochain. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

abbrev LeftIndex (a b c : ZMod 8) :=
  FusionTable.Index a b × (FusionTable.Index (a + b) c × Fin (realRepDim (a + b + c).val))
abbrev RightIndex (a b c : ZMod 8) :=
  FusionTable.Index b c × (FusionTable.Index a (b + c) × Fin (realRepDim (a + b + c).val))

/-- Raw-to-shifted source frame sign. -/
def leftFrameZ (a b c : ZMod 8) (r : FusionTable.Index a b) : ℤ :=
  (-1) ^ (realComputableNuBeta.data.nu (Multiplicative.ofAdd (a + b))
    (Multiplicative.ofAdd c) * FusionTable.indexParity a b r).val

/-- Raw-to-shifted target frame sign. -/
def rightFrameZ (a b c : ZMod 8) (r : FusionTable.Index b c) : ℤ :=
  (-1) ^ (realComputableNuBeta.data.nu (Multiplicative.ofAdd a)
    (Multiplicative.ofAdd (b + c)) * FusionTable.indexParity b c r).val

/-- The actual frozen connector, before the scalar beta correction. -/
def rawAssociatorZ (a b c : ZMod 8) : Matrix (RightIndex a b c) (LeftIndex a b c) ℤ :=
  fun r s => RealPChiKernel.connectorLinearCoeff a b c
    r.1.val r.2.1.val s.1.val s.2.1.val r.2.2.val s.2.2.val

/-- Integer matrix in the shifted binary-kernel frames. -/
def associatorZ (a b c : ZMod 8) : Matrix (RightIndex a b c) (LeftIndex a b c) ℤ :=
  fun r s => rightFrameZ a b c r.1 * rawAssociatorZ a b c r s * leftFrameZ a b c s.1

/-- Rational scalar multiplying the integer matrix. -/
def associatorScale (a b c : ZMod 8) : ℚ :=
  (dyadicRatValue (GaugeChi.realLeanBetaTable (Multiplicative.ofAdd a)
    (Multiplicative.ofAdd b) (Multiplicative.ofAdd c)))⁻¹

end RMod.BrundanEllis.Stacking.ReferenceCommutor
