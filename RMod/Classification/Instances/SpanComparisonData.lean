import RMod.Classification.Abstract.SpanSuperfunctor
import RMod.Classification.Instances.HomogeneousSpanPresentation
import RMod.Classification.Instances.HomogeneousRealization
import RMod.Classification.Instances.HomogeneousHomTransport

/-!
# Actual maps for comparison of two homogeneous spans

For every object, copy its selected parity list to the target generator.
Transport a morphism by its rectangular matrix and the given generator
endomorphism algebra equivalence. The construction uses full Hom spaces.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} (D : PiSuperfusion.{0, 0})
  {S : C.data.Obj} (T : D.data.Obj)

noncomputable def spanImageRealization (X : HomogeneousSpanCategory C S) :=
  homogeneousRealization D T (spanPresentation X).data.parity

noncomputable def spanImageObj (X : HomogeneousSpanCategory C S) :
    HomogeneousSpanCategory D.toWeaklyPointedSuperfusion T :=
  ⟨(spanImageRealization D T X).data.object,
    spanSize X, ⟨(spanImageRealization D T X).toHomogeneousSum⟩⟩

noncomputable def spanComparisonData
    (a : @End (LinearCategory C) _ S ≃ₐ[ℝ] @End (LinearCategory D.toWeaklyPointedSuperfusion) _ T) :
    SpanSuperfunctorData C D.toWeaklyPointedSuperfusion S T where
  obj := spanImageObj D T
  map {X Y} f := ObjectProperty.homMk (HomogeneousSum.transportHom a
    (spanPresentation X) (spanPresentation Y)
    (spanImageRealization D T X).toHomogeneousSum
    (spanImageRealization D T Y).toHomogeneousSum f.hom)

end RMod.Classification
