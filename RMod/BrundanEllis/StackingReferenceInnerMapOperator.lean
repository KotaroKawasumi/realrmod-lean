import RMod.BrundanEllis.StackingReferenceTensorCoordinateTransport
import RMod.BrundanEllis.StackingReferenceAtomOperator
import RMod.BrundanEllis.StackingReferenceHexagonMaps
import RMod.BrundanEllis.StackingReferenceInnerRightOperator

/-! Identify the actual inner exchange legs with their normalized kernel
operators, using the original tensor coefficients and row coordinates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT
attribute [local irreducible] uniformOperator Tensor.slotIndexEquiv Tensor.slots

/-- Tensoring the first binary exchange with the third identity gives the left inner operator. -/
theorem innerLeftMap_operator (a b c : ZMod 8) :
    ((leftTripleCoordinates b a c).toLinearMap.comp
      (labelOperator (a + b + c) (b + a + c) (leftAtomTensor a b c) (leftAtomTensor b a c)
        (leftAtomTensor_label a b c) (leftAtomTensor_label b a c)
        (congrArg (fun z => z + c) (add_comm a b)) (innerLeftMap a b c))).comp
        (leftTripleCoordinates a b c).symm.toLinearMap = innerLeftOperator a b c := by
  apply LinearMap.ext
  intro v
  funext r
  change leftTripleCoordinates b a c
    (rowCoefficientCast (congrArg (fun z => z + c) (add_comm a b))
      (uniformOperator (a + b + c) _ _ _ _ (innerLeftMap a b c)
        ((leftTripleCoordinates a b c).symm v))) r = _
  rw [leftTripleCoordinates_uniform]
  erw [uniformTensorCoordinates_leftCast (add_comm a b) c
    (atomTensor b a) (Obj.singleton (c, 0)) (fun _ => add_comm b a) (fun _ => rfl)]
  unfold innerLeftMap
  erw [uniformOperator_tensor_coordinate (a + b) c (atomTensor a b) (atomTensor b a)
    (Obj.singleton (c, 0)) (Obj.singleton (c, 0))
    (fun _ => rfl) (fun _ => add_comm b a) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => congrArg (fun z => z + c) (add_comm b a))]
  change kernelLabelCast (add_comm a b) rfl
    (∑ i : Fin (atomTensor a b).size, ∑ j : Fin 1,
      shiftedTensorOperator (a + b) c ((atomTensor a b).atom i).shift 0 0
        ((uniformExchange a b (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
          (fun _ => rfl) (fun _ => rfl) i ((atomRowIndex b a).symm r)).coeff (add_comm a b))
        ((Hom.id realDData (Obj.singleton (c, 0)) j (0 : Fin 1)).coeff rfl)
        (uniformTensorCoordinates (a + b) c (a + b + c) (atomTensor a b) (Obj.singleton (c, 0))
          (fun _ => rfl) (fun _ => rfl) ((leftTripleCoordinates a b c).symm v) i j)) = _
  simp only [Fin.sum_univ_one, singleton_id_coefficient, shiftedTensorOperator_right_one,
    uniformTensorCoordinates_leftTriple_symm, map_sum, kernelLabelCast_leftOperator]
  simp only [coefficientCast_one]
  simp_rw [atomUniformExchange_coefficient_real]
  simp only [Equiv.apply_symm_apply]
  rw [innerLeftOperator_apply]
  have hs (x : Coeff (b + a)) (w : RealCCarrier (b + a) c) :
      leftOperator (b + a) c (normalizingScalar a b • x) (Coeff.one c) w =
        normalizingScalar a b • leftOperator (b + a) c x (Coeff.one c) w :=
    realComputableShiftedRawDCT.laws.C.left_smul_left (b + a) c (normalizingScalar a b) x (Coeff.one c) w
  simp_rw [hs]
  rw [← Finset.smul_sum]
  apply congrArg (fun w => normalizingScalar a b • w)
  exact Equiv.sum_comp (atomRowIndex a b) (fun i =>
    leftOperator (b + a) c (fun u => (coefficientZ a b (forwardZ a b) r i u.val : ℝ))
      (Coeff.one c) (kernelLabelCast (add_comm a b) rfl (v i)))

/-- Tensoring the first identity with the last binary exchange gives the right inner operator. -/
theorem innerRightMap_operator (a b c : ZMod 8) :
    ((rightTripleCoordinates a c b).toLinearMap.comp
      (labelOperator (a + b + c) (a + c + b) (rightAtomTensor a b c) (rightAtomTensor a c b)
        (rightAtomTensor_label a b c) (rightAtomTensor_label a c b)
        ((add_assoc a b c).trans ((congrArg (fun z => a + z) (add_comm b c)).trans
          (add_assoc a c b).symm)) (innerRightMap a b c))).comp
        (rightTripleCoordinates a b c).symm.toLinearMap = innerRightOperator a b c := by
  rw [labelOperator_source_cast (add_assoc a b c)
    ((congrArg (fun z => a + z) (add_comm b c)).trans (add_assoc a c b).symm)]
  rw [labelOperator_target_cast (congrArg (fun z => a + z) (add_comm b c))
    (add_assoc a c b).symm (hY := fun _ => rfl)]
  apply LinearMap.ext
  intro v
  funext r
  change rightTripleCoordinates a c b
    (rowCoefficientCast (add_assoc a c b).symm
      (rowCoefficientCast (congrArg (fun z => a + z) (add_comm b c))
        (uniformOperator (a + (b + c)) _ _ _ _ (innerRightMap a b c)
          (rowCoefficientCast (add_assoc a b c) ((rightTripleCoordinates a b c).symm v))))) r = _
  apply (rightSliceCoordinates a c b).injective
  rw [innerRightOperator_apply, LinearEquiv.apply_symm_apply, rightTripleCoordinates_uniform_cast]
  erw [rowCoefficientCast_trans (add_assoc a c b).symm (add_assoc a c b)]
  change uniformTensorCoordinates a (c + b) (a + (c + b)) (Obj.singleton (a, 0)) (atomTensor c b)
    (fun _ => rfl) (fun _ => rfl)
    (rowCoefficientCast (congrArg (fun z => a + z) (add_comm b c))
      (uniformOperator (a + (b + c)) _ _ _ _ (innerRightMap a b c)
        (rowCoefficientCast (add_assoc a b c) ((rightTripleCoordinates a b c).symm v))))
    (0 : Fin 1) ((atomRowIndex c b).symm r) = _
  erw [uniformTensorCoordinates_rightCast a (add_comm b c)
    (Obj.singleton (a, 0)) (atomTensor c b) (fun _ => rfl) (fun _ => add_comm c b)]
  unfold innerRightMap
  erw [uniformOperator_tensor_coordinate a (b + c) (Obj.singleton (a, 0)) (Obj.singleton (a, 0))
    (atomTensor b c) (atomTensor c b)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => add_comm c b)
    (fun _ => rfl) (fun _ => congrArg (fun z => a + z) (add_comm c b))]
  change kernelLabelCast rfl (add_comm b c)
    (∑ i : Fin 1, ∑ j : Fin (atomTensor b c).size,
      shiftedTensorOperator a (b + c) 0 ((atomTensor b c).atom j).shift
        ((atomTensor c b).atom ((atomRowIndex c b).symm r)).shift
        ((Hom.id realDData (Obj.singleton (a, 0)) i (0 : Fin 1)).coeff rfl)
        ((uniformExchange b c (Obj.singleton (b, 0)) (Obj.singleton (c, 0))
          (fun _ => rfl) (fun _ => rfl) j ((atomRowIndex c b).symm r)).coeff (add_comm b c))
        (uniformTensorCoordinates a (b + c) (a + (b + c)) (Obj.singleton (a, 0)) (atomTensor b c)
          (fun _ => rfl) (fun _ => rfl)
          (rowCoefficientCast (add_assoc a b c) ((rightTripleCoordinates a b c).symm v)) i j)) = _
  simp only [Fin.sum_univ_one, singleton_id_coefficient, shiftedTensorOperator_left_one,
    uniformTensorCoordinates_rightTriple_symm, map_sum, kernelLabelCast_leftOperator, coefficientCast_one]
  simp_rw [atomUniformExchange_coefficient_real]
  simp only [Equiv.apply_symm_apply]
  have hs (x : Coeff (c + b)) (w : RealCCarrier a (c + b)) :
      leftOperator a (c + b) (Coeff.one a) (normalizingScalar b c • x) w =
        normalizingScalar b c • leftOperator a (c + b) (Coeff.one a) x w :=
    realComputableShiftedRawDCT.laws.C.left_smul_right a (c + b) (normalizingScalar b c) (Coeff.one a) x w
  simp_rw [hs]
  rw [← Finset.smul_sum]
  apply congrArg (fun w => normalizingScalar b c • w)
  exact Equiv.sum_comp (atomRowIndex b c) (fun i =>
    leftOperator a (c + b) (Coeff.one a) (fun u => (coefficientZ b c (forwardZ b c) r i u.val : ℝ))
      (kernelLabelCast rfl (add_comm b c) (rightSliceCoordinates a b c (v i))))

end RMod.BrundanEllis.Stacking.ReferenceCommutor
