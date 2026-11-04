import RMod.Classification.Instances.UnitTensorIntertwiner
import RMod.Classification.Proofs.UnitTensorComparisonCoherence
import RMod.Classification.Proofs.TensorComparisonExtensionEvaluation
import RMod.Classification.Proofs.TensorComparisonExt

/-!
# The two unit extensions agree on the entire unit component

Evaluation recovers the two canonical generator maps, which agree
exactly. The homogeneous matrix determination theorem extends this
equality to every pair of objects in the unit component.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}} (U : SimpleObject C)
  (E : SpanSuperequivalence A C A.data.tensorUnit U.data.object)
  {i : IsoData C.data C.data.tensorUnit (E.forwardFunctor.data.obj (spanGenerator A A.data.tensorUnit)).obj}
  (hi : EvenIsoLaws C.data i)

theorem unitTensorExtensions_equal
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A (unitSimple A) (unitSimple A)).data.object
      A.data.tensorUnit)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U U).data.object U.data.object)
    (X Y : HomogeneousSpanCategory A A.data.tensorUnit) :
    ((tensorComparisonExtension (leftUnitTensorIntertwiner (unitSimple A) U U E E hi hA hC)).data.app X Y).hom =
      ((tensorComparisonExtension (rightUnitTensorIntertwiner (unitSimple A) U U E E hi hA hC)).data.app X Y).hom := by
  let l := leftUnitTensorIntertwiner (unitSimple A) U U E E hi hA hC
  let r := rightUnitTensorIntertwiner (unitSimple A) U U E E hi hA hC
  let η := tensorComparisonExtension l
  let θ := tensorComparisonExtension r
  have hg : η.evaluate.data.hom = θ.evaluate.data.hom :=
    (tensorComparisonExtension_generator_hom l).trans
      ((unitTensorComparisons_equal E.forwardFunctor hi).trans
        (tensorComparisonExtension_generator_hom r).symm)
  have h := TensorComparison.hom_eq_smul_of_generator η θ 1
    (hg.trans (C.laws.one_smul _).symm) X Y
  exact h.trans (C.laws.one_smul _)

end RMod.Classification
