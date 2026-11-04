import RMod.Classification.Instances.SpanComparison

/-!
# A specified object comparison for the canonical span functor

Transport the source identity between the functor's chosen target
presentation and any prescribed target presentation of the same size.
The reverse transport gives the specified inverse component map.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

noncomputable def spanComparisonObjectIsoData {C : WeaklyPointedSuperfusion.{0, 0}}
    (D : PiSuperfusion.{0, 0}) {S : C.data.Obj} (T : D.data.Obj)
    (a : @End (LinearCategory C) _ S ≃ₐ[ℝ] @End (LinearCategory D.toWeaklyPointedSuperfusion) _ T)
    (X : HomogeneousSpanCategory C S) {Y : D.data.Obj}
    (B : HomogeneousSum D.data.toWeaklyPointedSuperfusionData T Y (spanSize X)) :
    IsoData D.data.toWeaklyPointedSuperfusionData (spanImageObj D T X).obj Y where
  hom := HomogeneousSum.transportHom a (spanPresentation X) (spanPresentation X)
    (spanImageRealization D T X).toHomogeneousSum B (𝟙 (X.obj : LinearCategory C))
  inv := HomogeneousSum.transportHom a (spanPresentation X) (spanPresentation X)
    B (spanImageRealization D T X).toHomogeneousSum (𝟙 (X.obj : LinearCategory C))

end RMod.Classification
