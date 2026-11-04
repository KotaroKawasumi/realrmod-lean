import RMod.Classification.Instances.TensorComparisonPresentations
import RMod.Classification.Proofs.HomogeneousSumComparison

/-!
# Inverse and grading laws of the extended tensor comparison

The two presentations have the same parity list by construction. The
general homogeneous comparison theorem therefore gives the actual
inverse identities and the common degree at every pair of objects.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  {E : SpanSuperfunctor C D S.data.object U.data.object}
  {H : SpanSuperfunctor C D T.data.object V.data.object}
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a : ZMod 2}
  (t : TensorIntertwiner S T U V E H N a)
  (X : HomogeneousSpanCategory C S.data.object) (Y : HomogeneousSpanCategory C T.data.object)

theorem tensorComparisonExtension_iso : IsoLaws D.data
    ((tensorComparisonExtensionData S T U V E.data H.data N.data a t.data).app X Y) :=
  HomogeneousSum.comparisonIsoLaws a (tensorComparisonSourcePresentation S T U V N X Y)
    (tensorComparisonTargetPresentation S T U V E H X Y) rfl t.data t.laws.toIsoLaws

theorem tensorComparisonExtension_hom_grade : D.data.IsHomogeneous a
    ((tensorComparisonExtensionData S T U V E.data H.data N.data a t.data).app X Y).hom :=
  HomogeneousSum.comparison_grade a (tensorComparisonSourcePresentation S T U V N X Y)
    (tensorComparisonTargetPresentation S T U V E H X Y) rfl t.data.hom t.laws.hom_grade

theorem tensorComparisonExtension_inv_grade : D.data.IsHomogeneous a
    ((tensorComparisonExtensionData S T U V E.data H.data N.data a t.data).app X Y).inv :=
  HomogeneousSum.comparison_grade a (tensorComparisonTargetPresentation S T U V E H X Y)
    (tensorComparisonSourcePresentation S T U V N X Y) rfl t.data.inv t.laws.inv_grade

end RMod.Classification
