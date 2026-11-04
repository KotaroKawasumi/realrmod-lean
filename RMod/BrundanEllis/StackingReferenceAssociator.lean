import RMod.BrundanEllis.StackingReferenceAssociatorData
import RMod.BrundanEllis.StackingReferenceNormalization

/-! Identify the executable associator with its finite coordinate matrix.
This bridge keeps the connector and both frame changes of the reference. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

abbrev LeftCarrier (a b c : ZMod 8) :=
  FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)
abbrev RightCarrier (a b c : ZMod 8) :=
  FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)

/-- Coordinates on the left-associated route. -/
def leftCoordinates (a b c : ZMod 8) : LeftCarrier a b c ≃ₗ[ℝ] (LeftIndex a b c → ℝ) where
  toFun v i := v i.1 i.2.1 i.2.2
  invFun v r s k := v (r, s, k)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinates on the right-associated route, using the same endpoint algebra. -/
def rightCoordinates (a b c : ZMod 8) : RightCarrier a b c ≃ₗ[ℝ] (RightIndex a b c → ℝ) where
  toFun v i := v i.1 i.2.1 i.2.2
  invFun v r s k := v (r, s, k)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The raw connector is already linear in its actual stored laws. -/
def rawAssociatorOperator (a b c : ZMod 8) :
    LeftCarrier a b c →ₗ[ℝ] RightCarrier a b c where
  toFun := realTHom a b c
  map_add' v w := realTLaws.hom_add a b c v w
  map_smul' r v := realTLaws.hom_smul a b c r v

private theorem rawFinSum_eq_sum {a : ZMod 8} {n : ℕ} (f : Fin n → Coeff a) :
    CData.rawFinSum (realDData.algebra a) f = ∑ r, f r := by
  change (List.ofFn f).sum = ∑ r, f r
  exact List.sum_ofFn

/-- A source coordinate vector is a coefficient basis in exactly one pair of rows. -/
theorem leftCoordinates_basis (a b c : ZMod 8) (s : LeftIndex a b c)
    (i : FusionTable.Index a b) (j : FusionTable.Index (a + b) c) :
    (leftCoordinates a b c).symm (Pi.single s 1) i j =
      if i = s.1 ∧ j = s.2.1 then RealPChiKernel.coefficientBasis (a + b + c) s.2.2 else 0 := by
  rcases s with ⟨s, t, u⟩
  funext k
  by_cases hi : i = s <;> by_cases hj : j = t <;>
    simp [leftCoordinates, Pi.single_apply, RealPChiKernel.coefficientBasis, hi, hj]

/-- Each integer entry is the corresponding coefficient of the actual raw map. -/
theorem rawAssociator_basis (a b c : ZMod 8) (r : RightIndex a b c) (s : LeftIndex a b c) :
    rightCoordinates a b c
      (rawAssociatorOperator a b c ((leftCoordinates a b c).symm (Pi.single s 1))) r =
        (rawAssociatorZ a b c r s : ℝ) := by
  change realTHom a b c ((leftCoordinates a b c).symm (Pi.single s 1)) r.1 r.2.1 r.2.2 = _
  simp only [realTHom, rawFinSum_eq_sum]
  simp_rw [leftCoordinates_basis]
  have hz (x : Coeff (a + b + c)) : Coeff.mul (a + b + c) x 0 = 0 := by
    with_unfolding_all exact Coeff.mul_zero (a + b + c) x
  simp only [ite_and, apply_ite, hz]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero]
  exact (RealPChiKernel.connectorLinearCoeff_cast a b c (r.1, r.2.1)
    (s.1, s.2.1) r.2.2 s.2.2).symm

/-- Equality of full operators follows from their coordinate basis values. -/
theorem rawAssociator_matrix (a b c : ZMod 8) :
    ((rightCoordinates a b c).toLinearMap.comp (rawAssociatorOperator a b c)).comp
      (leftCoordinates a b c).symm.toLinearMap =
        ((rawAssociatorZ a b c).map ((↑) : ℤ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (LeftIndex a b c)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  change rightCoordinates a b c
    (rawAssociatorOperator a b c ((leftCoordinates a b c).symm (Pi.single s 1))) r = _
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact rawAssociator_basis a b c r s

/-- The diagonal frame change on the source route. -/
def leftFrameOperator (a b c : ZMod 8) : LeftCarrier a b c →ₗ[ℝ] LeftCarrier a b c where
  toFun v r s := (leftFrameZ a b c r : ℝ) • v r s
  map_add' v w := by ext r s k; exact mul_add _ _ _
  map_smul' q v := by ext r s k; exact mul_left_comm _ _ _

/-- The diagonal frame change on the target route. -/
def rightFrameOperator (a b c : ZMod 8) : RightCarrier a b c →ₗ[ℝ] RightCarrier a b c where
  toFun v r s := (rightFrameZ a b c r : ℝ) • v r s
  map_add' v w := by ext r s k; exact mul_add _ _ _
  map_smul' q v := by ext r s k; exact mul_left_comm _ _ _

/-- Shifted and rescaled connector, retaining all three prescribed corrections. -/
def associatorOperator (a b c : ZMod 8) : LeftCarrier a b c →ₗ[ℝ] RightCarrier a b c :=
  (associatorScale a b c : ℝ) •
    ((rightFrameOperator a b c).comp ((rawAssociatorOperator a b c).comp (leftFrameOperator a b c)))

theorem leftFrameZ_cast (a b c : ZMod 8) (r : FusionTable.Index a b) :
    (leftFrameZ a b c r : ℝ) = leftRouteFrameSign realCData realComputableNuBeta.data a b c r := by
  simp only [leftFrameZ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact (paritySign_pow _).symm

theorem rightFrameZ_cast (a b c : ZMod 8) (r : FusionTable.Index b c) :
    (rightFrameZ a b c r : ℝ) = rightRouteFrameSign realCData realComputableNuBeta.data a b c r := by
  simp only [rightFrameZ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact (paritySign_pow _).symm

/-- The scalar is the inverse of the actual stored reference beta. -/
theorem associatorScale_actual (a b c : ZMod 8) :
    (associatorScale a b c : ℝ) = (↑(shiftBeta realComputableNuBeta.data a b c)⁻¹ : ℝ) := by
  let d := GaugeChi.realLeanBetaTable (Multiplicative.ofAdd a)
    (Multiplicative.ofAdd b) (Multiplicative.ofAdd c)
  change (↑((dyadicRatValue d)⁻¹) : ℝ) = (↑(dyadicRatValue d⁻¹) : ℝ)
  rw [dyadicRatValue_inv]

/-- The source frame is diagonal on the chosen homogeneous basis. -/
theorem leftFrame_basis (a b c : ZMod 8) (s : LeftIndex a b c) :
    leftFrameOperator a b c ((leftCoordinates a b c).symm (Pi.single s 1)) =
      (leftFrameZ a b c s.1 : ℝ) • ((leftCoordinates a b c).symm (Pi.single s 1)) := by
  ext i j k
  change (leftFrameZ a b c i : ℝ) * ((leftCoordinates a b c).symm (Pi.single s 1) i j k) =
    (leftFrameZ a b c s.1 : ℝ) * ((leftCoordinates a b c).symm (Pi.single s 1) i j k)
  by_cases hi : i = s.1
  · rw [hi]
  · rw [leftCoordinates_basis]
    simp [hi]

/-- Full matrix of the shifted associator in its actual binary-kernel frames. -/
theorem associator_matrix (a b c : ZMod 8) :
    ((rightCoordinates a b c).toLinearMap.comp (associatorOperator a b c)).comp
      (leftCoordinates a b c).symm.toLinearMap =
        ((associatorScale a b c : ℝ) • (associatorZ a b c).map ((↑) : ℤ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (LeftIndex a b c)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one, associatorOperator, LinearMap.smul_apply, map_smul,
    leftFrame_basis]
  change (associatorScale a b c : ℝ) *
      ((leftFrameZ a b c s.1 : ℝ) * ((rightFrameZ a b c r.1 : ℝ) *
        rightCoordinates a b c (rawAssociatorOperator a b c
          ((leftCoordinates a b c).symm (Pi.single s 1))) r)) = _
  rw [rawAssociator_basis]
  change (associatorScale a b c : ℝ) *
    ((leftFrameZ a b c s.1 : ℝ) * ((rightFrameZ a b c r.1 : ℝ) * (rawAssociatorZ a b c r s : ℝ))) =
      (associatorScale a b c : ℝ) *
        ((rightFrameZ a b c r.1 * rawAssociatorZ a b c r s * leftFrameZ a b c s.1 : ℤ) : ℝ)
  push_cast
  ring

/-- The matrix presentation is the existing shifted connector, not a new associator. -/
theorem associator_actual (a b c : ZMod 8) (v : LeftCarrier a b c) :
    associatorOperator a b c v =
      realComputableShiftedRawDCT.data.T.rightToCoord a b c
        (realComputableShiftedRawDCT.data.T.hom a b c
          (realComputableShiftedRawDCT.data.T.leftOfCoord a b c v)) := by
  have hf : leftFrameOperator a b c v =
      leftRouteFrameInv realDData realCData realComputableNuBeta.data a b c v := by
    funext i j k
    change (leftFrameZ a b c i : ℝ) * v i j k =
      leftRouteFrameSign realCData realComputableNuBeta.data a b c i * v i j k
    rw [leftFrameZ_cast]
  funext i j k
  change (associatorScale a b c : ℝ) * ((rightFrameZ a b c i : ℝ) *
      realTHom a b c (leftFrameOperator a b c v) i j k) =
    rightRouteFrameSign realCData realComputableNuBeta.data a b c i *
      ((↑(shiftBeta realComputableNuBeta.data a b c)⁻¹ : ℝ) *
        realTHom a b c
          (leftRouteFrameInv realDData realCData realComputableNuBeta.data a b c v) i j k)
  rw [hf, associatorScale_actual, rightFrameZ_cast]
  ring

end RMod.BrundanEllis.Stacking.ReferenceCommutor
