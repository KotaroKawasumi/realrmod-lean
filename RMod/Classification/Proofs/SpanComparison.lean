import RMod.Classification.Instances.SpanComparisonData
import RMod.Classification.Proofs.HomogeneousHomTransport

/-!
# The comparison maps satisfy the superfunctor laws

Rectangular matrix transport supplies identity, composition and linearity.
The target realization has exactly the requested parities, so the
graded generator algebra comparison proves preservation of every degree.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} (D : PiSuperfusion.{0, 0})
  {S : C.data.Obj} (T : D.data.Obj)
  (a : @End (LinearCategory C) _ S ≃ₐ[ℝ] @End (LinearCategory D.toWeaklyPointedSuperfusion) _ T)

theorem spanComparisonLaws
    (ha : ∀ b f, C.data.IsHomogeneous b f → D.data.IsHomogeneous b (a f)) :
    SpanSuperfunctorLaws C D.toWeaklyPointedSuperfusion S T (spanComparisonData D T a) where
  map_id X := by
    apply ObjectProperty.hom_ext
    exact HomogeneousSum.transportHom_id a (spanPresentation X) _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact HomogeneousSum.transportHom_comp a _ _ _ _ _ _ f.hom g.hom
  map_zero X Y := by
    apply ObjectProperty.hom_ext
    exact (HomogeneousSum.transportHom a (spanPresentation X) (spanPresentation Y) _ _).map_zero
  map_add f g := by
    apply ObjectProperty.hom_ext
    exact (HomogeneousSum.transportHom a _ _ _ _).map_add f.hom g.hom
  map_smul r f := by
    apply ObjectProperty.hom_ext
    exact (HomogeneousSum.transportHom a _ _ _ _).map_smul r f.hom
  map_grade {X Y b} f hf :=
    HomogeneousSum.transportHom_grade a (spanPresentation X) (spanPresentation Y)
      (spanImageRealization D T X).toHomogeneousSum (spanImageRealization D T Y).toHomogeneousSum
      ha (spanImageRealization D T X).laws.parity (spanImageRealization D T Y).laws.parity hf

theorem spanComparison_grade_iff
    (ha : ∀ b f, D.data.IsHomogeneous b (a f) ↔ C.data.IsHomogeneous b f)
    {X Y : HomogeneousSpanCategory C S} {b : ZMod 2} (f : X ⟶ Y) :
    D.data.IsHomogeneous b ((spanComparisonData D T a).map f).hom ↔ C.data.IsHomogeneous b f.hom :=
  HomogeneousSum.transportHom_grade_iff a (spanPresentation X) (spanPresentation Y)
    (spanImageRealization D T X).toHomogeneousSum (spanImageRealization D T Y).toHomogeneousSum
    ha (spanImageRealization D T X).laws.parity (spanImageRealization D T Y).laws.parity f.hom

end RMod.Classification
