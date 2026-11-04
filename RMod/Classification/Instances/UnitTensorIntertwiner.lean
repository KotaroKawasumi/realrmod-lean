import RMod.Classification.Instances.TensorProductTransport
import RMod.Classification.Proofs.UnitTensorComparison
import RMod.Classification.Abstract.TensorIntertwiner
import RMod.Classification.Instances.SimpleOrbits

/-!
# Even generator intertwiners at the unit component

Identity changes of homogeneous span do not alter the component maps.
The explicit unitor comparisons consequently have exactly the tensor
intertwiner source and target. Their unsigned naturality is the signed
naturality law in degree zero.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}} (T : SimpleObject A) (U V : SimpleObject C)
  (E : SpanSuperequivalence A C A.data.tensorUnit U.data.object)
  (H : SpanSuperequivalence A C T.data.object V.data.object)
  {i : IsoData C.data C.data.tensorUnit (E.forwardFunctor.data.obj (spanGenerator A A.data.tensorUnit)).obj}
  (hi : EvenIsoLaws C.data i)

include hi

theorem leftUnitTensorIntertwinerLaws
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A (unitSimple A) T).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object V.data.object) :
    TensorIntertwinerLaws (unitSimple A) T U V
      (M := (tensorProductTransport (unitSimple A) T T U V V H hA hC).forwardFunctor.data) 0
      (leftUnitTensorComparisonData T E.forwardFunctor.data H.forwardFunctor.data i) where
  toIsoLaws := (leftUnitTensorComparison_evenIso T E.forwardFunctor H.forwardFunctor hi).toIsoLaws
  hom_grade := (leftUnitTensorComparison_evenIso T E.forwardFunctor H.forwardFunctor hi).hom_even
  inv_grade := (leftUnitTensorComparison_evenIso T E.forwardFunctor H.forwardFunctor hi).inv_even
  intertwines f g _ _ := by
    simp only [zero_mul, ZMod.val_zero, pow_zero, C.laws.one_smul]
    exact leftUnitTensorComparison_naturality T E.forwardFunctor H.forwardFunctor hi f g

def leftUnitTensorIntertwiner
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A (unitSimple A) T).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object V.data.object) :
    TensorIntertwiner (unitSimple A) T U V E.forwardFunctor H.forwardFunctor
      (tensorProductTransport (unitSimple A) T T U V V H hA hC).forwardFunctor 0 :=
  ⟨leftUnitTensorComparisonData T E.forwardFunctor.data H.forwardFunctor.data i,
    leftUnitTensorIntertwinerLaws T U V E H hi hA hC⟩

theorem rightUnitTensorIntertwinerLaws
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A T (unitSimple A)).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C V U).data.object V.data.object) :
    TensorIntertwinerLaws T (unitSimple A) V U
      (M := (tensorProductTransport T (unitSimple A) T V U V H hA hC).forwardFunctor.data) 0
      (rightUnitTensorComparisonData T H.forwardFunctor.data E.forwardFunctor.data i) where
  toIsoLaws := (rightUnitTensorComparison_evenIso T H.forwardFunctor E.forwardFunctor hi).toIsoLaws
  hom_grade := (rightUnitTensorComparison_evenIso T H.forwardFunctor E.forwardFunctor hi).hom_even
  inv_grade := (rightUnitTensorComparison_evenIso T H.forwardFunctor E.forwardFunctor hi).inv_even
  intertwines g f _ _ := by
    simp only [zero_mul, ZMod.val_zero, pow_zero, C.laws.one_smul]
    exact rightUnitTensorComparison_naturality T E.forwardFunctor H.forwardFunctor hi g f

def rightUnitTensorIntertwiner
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A T (unitSimple A)).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C V U).data.object V.data.object) :
    TensorIntertwiner T (unitSimple A) V U H.forwardFunctor E.forwardFunctor
      (tensorProductTransport T (unitSimple A) T V U V H hA hC).forwardFunctor 0 :=
  ⟨rightUnitTensorComparisonData T H.forwardFunctor.data E.forwardFunctor.data i,
    rightUnitTensorIntertwinerLaws T U V E H hi hA hC⟩

end RMod.Classification
