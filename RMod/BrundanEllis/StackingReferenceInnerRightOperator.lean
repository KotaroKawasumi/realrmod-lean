import RMod.BrundanEllis.StackingReferenceInnerOperator
import RMod.BrundanEllis.StackingReferenceOuterOperator

/-! The right inner crossing acts in the second algebra slot. Reassociation
of the endpoint label is tracked before and after that action. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

/-- A right-route slice differs from its fusion kernel only by label parentheses. -/
def rightSliceCoordinates (a b c : ZMod 8) :
    (FusionTable.Index a (b + c) → Coeff (a + b + c)) ≃ₗ[ℝ] RealCCarrier a (b + c) :=
  LinearEquiv.piCongrRight fun _ => coefficientCast (add_assoc a b c)

/-- The reindexed basis keeps the inner row and both numerical coordinate positions. -/
theorem rightSliceCoordinates_basis (a b c : ZMod 8) (s : RightIndex a b c)
    (r : FusionTable.Index b c) :
    rightSliceCoordinates a b c ((rightCoordinates a b c).symm (Pi.single s 1) r) =
      if r = s.1 then
        (coordinates a (b + c)).symm (Pi.single
          (s.2.1, Fin.cast (congrArg (fun z : ZMod 8 => realRepDim z.val) (add_assoc a b c)) s.2.2) 1)
      else 0 := by
  funext j
  change coefficientCast (add_assoc a b c)
    ((rightCoordinates a b c).symm (Pi.single s 1) r j) = _
  rw [rightCoordinates_basis]
  simp only [ite_and, apply_ite, map_zero, coefficientCast_basis]
  by_cases h : r = s.1
  · simp only [h, if_true]
    exact (coordinates_basis a (b + c)
      (s.2.1, Fin.cast (congrArg (fun z : ZMod 8 => realRepDim z.val) (add_assoc a b c)) s.2.2) j).symm
  · simp [h]

/-- Reversing a coefficient-label equality gives the inverse linear equivalence. -/
theorem coefficientCast_symm_apply {a b : ZMod 8} (h : a = b) (x : Coeff b) :
    (coefficientCast h).symm x = coefficientCast h.symm x := by
  cases h
  rfl

/-- Tensor the identity of the first atom with the exchange of the inner pair. -/
def innerRightOperator (a b c : ZMod 8) : RightCarrier a b c →ₗ[ℝ] RightCarrier a c b :=
  LinearMap.pi fun r => (rightSliceCoordinates a c b).symm.toLinearMap.comp
    (normalizingScalar b c • ∑ s : FusionTable.Index b c,
      (leftOperator a (c + b) (Coeff.one a)
        (fun u => (coefficientZ b c (forwardZ b c) r s u.val : ℝ))).comp
        ((kernelLabelCast rfl (add_comm b c)).toLinearMap.comp
          ((rightSliceCoordinates a b c).toLinearMap.comp (LinearMap.proj s))))

/-- The actual slot action, with both coefficient-label transports visible. -/
theorem innerRightOperator_apply (a b c : ZMod 8) (v : RightCarrier a b c)
    (r : FusionTable.Index c b) :
    innerRightOperator a b c v r = (rightSliceCoordinates a c b).symm
      (normalizingScalar b c • ∑ s : FusionTable.Index b c,
        leftOperator a (c + b) (Coeff.one a)
          (fun u => (coefficientZ b c (forwardZ b c) r s u.val : ℝ))
          (kernelLabelCast rfl (add_comm b c) (rightSliceCoordinates a b c (v s)))) := by
  simp only [innerRightOperator, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]

/-- The inner-right integer matrix is the complete basis action of this operator. -/
theorem innerRightOperator_basis (a b c : ZMod 8) (r : RightIndex a c b) (s : RightIndex a b c) :
    rightCoordinates a c b
      (innerRightOperator a b c ((rightCoordinates a b c).symm (Pi.single s 1))) r =
        normalizingScalar b c * (innerRightZ a b c r s : ℝ) := by
  change (innerRightOperator a b c _ r.1) r.2.1 r.2.2 = _
  rw [innerRightOperator_apply]
  simp_rw [rightSliceCoordinates_basis, apply_ite, map_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [kernelLabelCast_basis]
  change (coefficientCast (add_assoc a c b)).symm
    (normalizingScalar b c • leftOperator a (c + b) (Coeff.one a) _
      ((coordinates a (c + b)).symm _) r.2.1) r.2.2 = _
  rw [coefficientCast_symm_apply, coefficientCast_apply]
  change normalizingScalar b c * coordinates a (c + b)
    (leftOperator a (c + b) (Coeff.one a) _ ((coordinates a (c + b)).symm _))
      (r.2.1, Fin.cast (congrArg (fun z : ZMod 8 => realRepDim z.val) (add_assoc a c b)) r.2.2) = _
  rw [rightOperator_integer_basis]
  congr 1
  simp only [innerRightZ, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro u _
  simp only [rightActionZ, Fin.val_cast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- Linear extension identifies the entire right inner leg. -/
theorem innerRightOperator_matrix (a b c : ZMod 8) :
    ((rightCoordinates a c b).toLinearMap.comp (innerRightOperator a b c)).comp
      (rightCoordinates a b c).symm.toLinearMap =
      (normalizingScalar b c • (innerRightZ a b c).map ((↑) : ℤ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (RightIndex a b c)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  change rightCoordinates a c b
    (innerRightOperator a b c ((rightCoordinates a b c).symm (Pi.single s 1))) r = _
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact innerRightOperator_basis a b c r s

end RMod.BrundanEllis.Stacking.ReferenceCommutor
