import RMod.Classification.Instances.UnitTensorComparisonExtension
import RMod.Classification.Proofs.UnitTensorExtensionCoherence
import RMod.Classification.Proofs.TensorComparisonEquality

/-! # Exact compatibility of normalized-generator unit comparisons -/

set_option autoImplicit false

namespace RMod.Classification

theorem unitTensorComparisons_ofEq_equal {A C : WeaklyPointedSuperfusion.{0, 0}}
    (S : SimpleObject A) (U : SimpleObject C)
    (E : SpanSuperequivalence A C S.data.object U.data.object)
    {i : IsoData C.data C.data.tensorUnit (E.forwardFunctor.data.obj (spanGenerator A S.data.object)).obj}
    (hi : EvenIsoLaws C.data i) (hS : S = unitSimple A)
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A S S).data.object S.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U U).data.object U.data.object) :
    leftUnitTensorComparison S S U U E E hi hS hA hC = rightUnitTensorComparison S S U U E E hi hS hA hC := by
  subst S
  apply TensorComparison.ext
  exact unitTensorExtensions_equal U E hi hA hC

end RMod.Classification
