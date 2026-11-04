import RMod.BrundanEllis.StackingReferenceOuterOperator

/-! The reverse reference connector in the same frame coordinates as the
forward associator. Its matrix retains the stored inverse denominator. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT
open RMod.ConstructiveConnectorTable RealPChiKernel

/-- Linear action of the existing unshifted inverse connector. -/
def rawAssociatorInverseOperator (a b c : ZMod 8) : RightCarrier a b c →ₗ[ℝ] LeftCarrier a b c where
  toFun := realTInv a b c
  map_add' v w := realTLaws.inv_add a b c v w
  map_smul' r v := realTLaws.inv_smul a b c r v

/-- Integer numerator before the two parity frame changes. -/
def rawAssociatorInverseZ (a b c : ZMod 8) : Matrix (LeftIndex a b c) (RightIndex a b c) ℤ :=
  fun r s => leftMulBasisCoeff (a + b + c).val
    (fun h => coeffGet (inverseNumeratorCoeff a b c)
      (sourceFramePosition a b c r.1.val r.2.1.val)
      (targetFramePosition a b c s.1.val s.2.1.val) h) s.2.2.val r.2.2.val

private theorem rawFinSum_eq_sum {a : ZMod 8} {n : ℕ} (f : Fin n → Coeff a) :
    CData.rawFinSum (realDData.algebra a) f = ∑ i, f i := by
  change (List.ofFn f).sum = ∑ i, f i
  exact List.sum_ofFn

/-- The inverse connector acts on each basis vector by its stored numerator. -/
theorem rawAssociatorInverse_basis (a b c : ZMod 8) (r : LeftIndex a b c) (s : RightIndex a b c) :
    leftCoordinates a b c
      (rawAssociatorInverseOperator a b c ((rightCoordinates a b c).symm (Pi.single s 1))) r =
        realTInverseScale a b c * (rawAssociatorInverseZ a b c r s : ℝ) := by
  change realTInv a b c ((rightCoordinates a b c).symm (Pi.single s 1)) r.1 r.2.1 r.2.2 = _
  simp only [realTInv, rawFinSum_eq_sum]
  simp_rw [rightCoordinates_basis]
  have hz (x : Coeff (a + b + c)) : Coeff.mul (a + b + c) x 0 = 0 := by
    with_unfolding_all exact Coeff.mul_zero (a + b + c) x
  simp only [ite_and, apply_ite, hz, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero]
  unfold realTInverseEntry
  simp only [← sourceFramePosition_eq_realTLeftPosition, ← targetFramePosition_eq_realTRightPosition]
  change (Coeff.mul (a + b + c)
    (Coeff.smul (a + b + c) (realTInverseScale a b c)
      (fun e => (coeffGet (inverseNumeratorCoeff a b c)
        (sourceFramePosition a b c r.1.val r.2.1.val)
        (targetFramePosition a b c s.1.val s.2.1.val) e.val : ℝ)))
    (coefficientBasis (a + b + c) s.2.2)) r.2.2 = _
  rw [Coeff.smul_mul]
  change realTInverseScale a b c * _ = _
  congr 1
  exact (leftMulBasisCoeff_cast (a + b + c)
    (fun h => coeffGet (inverseNumeratorCoeff a b c)
      (sourceFramePosition a b c r.1.val r.2.1.val)
      (targetFramePosition a b c s.1.val s.2.1.val) h) s.2.2 r.2.2).symm

/-- Reverse both frames and the beta normalization. -/
def associatorInverseOperator (a b c : ZMod 8) : RightCarrier a b c →ₗ[ℝ] LeftCarrier a b c :=
  (associatorScale a b c : ℝ)⁻¹ •
    ((leftFrameOperator a b c).comp ((rawAssociatorInverseOperator a b c).comp (rightFrameOperator a b c)))

/-- The target-route frame is diagonal on its coordinate basis. -/
theorem rightFrame_basis (a b c : ZMod 8) (s : RightIndex a b c) :
    rightFrameOperator a b c ((rightCoordinates a b c).symm (Pi.single s 1)) =
      (rightFrameZ a b c s.1 : ℝ) • ((rightCoordinates a b c).symm (Pi.single s 1)) := by
  ext i j k
  change (rightFrameZ a b c i : ℝ) * ((rightCoordinates a b c).symm (Pi.single s 1) i j k) =
    (rightFrameZ a b c s.1 : ℝ) * ((rightCoordinates a b c).symm (Pi.single s 1) i j k)
  by_cases hi : i = s.1
  · rw [hi]
  · rw [rightCoordinates_basis]
    simp [hi]

/-- Full normalized inverse matrix, including the explicit connector denominator. -/
theorem associatorInverse_matrix (a b c : ZMod 8) :
    ((leftCoordinates a b c).toLinearMap.comp (associatorInverseOperator a b c)).comp
      (rightCoordinates a b c).symm.toLinearMap =
      (((associatorScale a b c : ℝ)⁻¹ * realTInverseScale a b c) •
        (associatorInverseZ a b c).map ((↑) : ℤ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (RightIndex a b c)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one, associatorInverseOperator, LinearMap.smul_apply,
    map_smul, rightFrame_basis]
  change (associatorScale a b c : ℝ)⁻¹ *
    ((rightFrameZ a b c s.1 : ℝ) * ((leftFrameZ a b c r.1 : ℝ) *
      leftCoordinates a b c (rawAssociatorInverseOperator a b c
        ((rightCoordinates a b c).symm (Pi.single s 1))) r)) = _
  rw [rawAssociatorInverse_basis]
  change (associatorScale a b c : ℝ)⁻¹ *
      ((rightFrameZ a b c s.1 : ℝ) * ((leftFrameZ a b c r.1 : ℝ) *
        (realTInverseScale a b c * (rawAssociatorInverseZ a b c r s : ℝ)))) =
    ((associatorScale a b c : ℝ)⁻¹ * realTInverseScale a b c) *
      (↑(leftFrameZ a b c r.1 * rawAssociatorInverseZ a b c r s * rightFrameZ a b c s.1) : ℝ)
  push_cast
  ring

/-- The operator is the actual shifted inverse connector in coordinate form. -/
theorem associatorInverse_actual (a b c : ZMod 8) (v : RightCarrier a b c) :
    associatorInverseOperator a b c v =
      realComputableShiftedRawDCT.data.T.leftToCoord a b c
        (realComputableShiftedRawDCT.data.T.inv a b c
          (realComputableShiftedRawDCT.data.T.rightOfCoord a b c v)) := by
  have hf : rightFrameOperator a b c v =
      rightRouteFrameInv realDData realCData realComputableNuBeta.data a b c v := by
    funext i j k
    change (rightFrameZ a b c i : ℝ) * v i j k =
      rightRouteFrameSign realCData realComputableNuBeta.data a b c i * v i j k
    rw [rightFrameZ_cast]
  have hb : (associatorScale a b c : ℝ)⁻¹ = (↑(shiftBeta realComputableNuBeta.data a b c) : ℝ) := by
    rw [associatorScale_actual]
    simp only [Units.val_inv_eq_inv_val, inv_inv]
  funext i j k
  change (associatorScale a b c : ℝ)⁻¹ * ((leftFrameZ a b c i : ℝ) *
      realTInv a b c (rightFrameOperator a b c v) i j k) =
    leftRouteFrameSign realCData realComputableNuBeta.data a b c i *
      ((↑(shiftBeta realComputableNuBeta.data a b c) : ℝ) *
        realTInv a b c (rightRouteFrameInv realDData realCData realComputableNuBeta.data a b c v) i j k)
  rw [hf, hb, leftFrameZ_cast]
  ring

/-- The reverse operator is a left inverse of the given associator operator. -/
theorem associatorInverseOperator_hom (a b c : ZMod 8) (v : LeftCarrier a b c) :
    associatorInverseOperator a b c (associatorOperator a b c v) = v := by
  rw [associatorInverse_actual, associator_actual,
    realComputableShiftedRawDCT.laws.T.right_ofCoord_toCoord,
    realComputableShiftedRawDCT.laws.T.inv_hom_id,
    realComputableShiftedRawDCT.laws.T.left_toCoord_ofCoord]

/-- It is also a right inverse, so the coordinate comparison is an isomorphism. -/
theorem associatorOperator_inv (a b c : ZMod 8) (v : RightCarrier a b c) :
    associatorOperator a b c (associatorInverseOperator a b c v) = v := by
  rw [associator_actual, associatorInverse_actual,
    realComputableShiftedRawDCT.laws.T.left_ofCoord_toCoord,
    realComputableShiftedRawDCT.laws.T.hom_inv_id,
    realComputableShiftedRawDCT.laws.T.right_toCoord_ofCoord]

end RMod.BrundanEllis.Stacking.ReferenceCommutor
