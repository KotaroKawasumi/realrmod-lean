import RMod.Classification.Instances.UnitTensorIntertwiner
import RMod.Classification.Instances.TensorComparisonExtension
import RMod.Classification.Proofs.SimpleObjectExt

/-!
# Extending unit comparisons across the whole unit component

Once the source generator is the actual unit, the specified even unit
isomorphism supplies the generator intertwiner. Its proved signed matrix
extension gives the comparison on every object in both components.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T : SimpleObject A) (U V : SimpleObject C)
  (E : SpanSuperequivalence A C S.data.object U.data.object)
  (H : SpanSuperequivalence A C T.data.object V.data.object)
  {i : IsoData C.data C.data.tensorUnit (E.forwardFunctor.data.obj (spanGenerator A S.data.object)).obj}
  (hi : EvenIsoLaws C.data i) (hS : S = unitSimple A)

include hi hS

theorem exists_leftUnitTensorComparison
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A S T).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object V.data.object) :
    Nonempty (TensorComparison S T U V E.forwardFunctor H.forwardFunctor
      (tensorProductTransport S T T U V V H hA hC).forwardFunctor 0) := by
  subst S
  exact ⟨tensorComparisonExtension (leftUnitTensorIntertwiner T U V E H hi hA hC)⟩

theorem exists_rightUnitTensorComparison
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A T S).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C V U).data.object V.data.object) :
    Nonempty (TensorComparison T S V U H.forwardFunctor E.forwardFunctor
      (tensorProductTransport T S T V U V H hA hC).forwardFunctor 0) := by
  subst S
  exact ⟨tensorComparisonExtension (rightUnitTensorIntertwiner T U V E H hi hA hC)⟩

end RMod.Classification
