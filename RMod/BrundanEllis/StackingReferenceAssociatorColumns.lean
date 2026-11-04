import RMod.BrundanEllis.StackingReferenceAssociator
import Superfusion.RMod.FromRawDCT.RealAssociator

/-! Unit columns of the normalized connector recover the actual coefficients
used in the raw associator. The matrix identity is therefore a statement
about the fixed reference data, including both shift frames and beta. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- A ternary row unit is the coefficient basis at the algebra's unit index. -/
theorem leftCoordinates_delta (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    (leftCoordinates a b c).symm
      (Pi.single (r, s, RealPChiKernel.coefficientUnitIndex (a + b + c)) 1) =
      Associator.leftDelta realComputableShiftedRawDCT.data a b c r s := by
  funext i j
  rw [leftCoordinates_basis, RealPChiRouteBridge.coefficientBasis_unit]
  simp only [Associator.leftDelta, ite_and]
  rfl

/-- Every actual connector coefficient is a column of the normalized matrix. -/
theorem associator_coefficient (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c)
    (t : FusionTable.Index b c) (u : FusionTable.Index a (b + c))
    (k : Fin (realRepDim (a + b + c).val)) :
    (Associator.homCoefficient realComputableShiftedRawDCT.data a b c r s t u) k =
      (associatorScale a b c : ℝ) *
        (associatorZ a b c (t, u, k)
          (r, s, RealPChiKernel.coefficientUnitIndex (a + b + c)) : ℝ) := by
  have h := congrArg (fun F : (LeftIndex a b c → ℝ) →ₗ[ℝ] (RightIndex a b c → ℝ) =>
      F (Pi.single (r, s, RealPChiKernel.coefficientUnitIndex (a + b + c)) 1) (t, u, k))
    (associator_matrix a b c)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one] at h
  rw [leftCoordinates_delta, associator_actual] at h
  exact h

/-- The same operator acts by left multiplication with those stored coefficients. -/
theorem associatorOperator_coefficients (a b c : ZMod 8) (v : LeftCarrier a b c)
    (t : FusionTable.Index b c) (u : FusionTable.Index a (b + c)) :
    associatorOperator a b c v t u =
      CData.rawFinSum (realDData.algebra (a + b + c)) (fun r : FusionTable.Index a b =>
        CData.rawFinSum (realDData.algebra (a + b + c)) (fun s : FusionTable.Index (a + b) c =>
          Coeff.mul (a + b + c)
            (Associator.homCoefficient realComputableShiftedRawDCT.data a b c r s t u) (v r s))) := by
  rw [associator_actual, Associator.hom_toCoord_eq_matrix _ realComputableShiftedRawDCT.laws]
  erw [realComputableShiftedRawDCT.laws.T.left_toCoord_ofCoord]
  rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
