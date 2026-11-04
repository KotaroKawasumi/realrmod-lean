import RMod.Classification.Instances.UnitTensorIntertwiner
import RMod.Classification.Instances.TensorComparisonExtension

/-!
# Specified unit comparisons with a normalized simple generator

Transport the already constructed comparison along equality of the
simple generator with the unit. All map data and their laws come from
the separately defined unit intertwiner and matrix extension; no new
choice of a comparison or of a scalar is made here.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T : SimpleObject A) (U V : SimpleObject C)
  (E : SpanSuperequivalence A C S.data.object U.data.object)
  (H : SpanSuperequivalence A C T.data.object V.data.object)
  {i : IsoData C.data C.data.tensorUnit (E.forwardFunctor.data.obj (spanGenerator A S.data.object)).obj}
  (hi : EvenIsoLaws C.data i) (hS : S = unitSimple A)

noncomputable def leftUnitTensorComparison
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A S T).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object V.data.object) :
    TensorComparison S T U V E.forwardFunctor H.forwardFunctor
      (tensorProductTransport S T T U V V H hA hC).forwardFunctor 0 := by
  subst S
  exact tensorComparisonExtension (leftUnitTensorIntertwiner T U V E H hi hA hC)

noncomputable def rightUnitTensorComparison
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A T S).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C V U).data.object V.data.object) :
    TensorComparison T S V U H.forwardFunctor E.forwardFunctor
      (tensorProductTransport T S T V U V H hA hC).forwardFunctor 0 := by
  subst S
  exact tensorComparisonExtension (rightUnitTensorIntertwiner T U V E H hi hA hC)

end RMod.Classification
