import RMod.Classification.Proofs.SpanComparison
import RMod.Classification.Instances.SpanSuperfunctor
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# The completed, fully faithful component comparison functor

The inverse linear map on each Hom space is the actual inverse of matrix
transport. Mathlib's fully faithful witness retains these preimages.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} (D : PiSuperfusion.{0, 0})
  {S : C.data.Obj} (T : D.data.Obj)
  (a : @End (LinearCategory C) _ S ≃ₐ[ℝ] @End (LinearCategory D.toWeaklyPointedSuperfusion) _ T)
  (ha : ∀ b f, C.data.IsHomogeneous b f → D.data.IsHomogeneous b (a f))

noncomputable def spanComparison : SpanSuperfunctor C D.toWeaklyPointedSuperfusion S T :=
  ⟨spanComparisonData D T a, spanComparisonLaws D T a ha⟩

noncomputable def spanComparisonFullyFaithful : (spanComparison D T a ha).toFunctor.FullyFaithful where
  preimage {X Y} f := ObjectProperty.homMk ((HomogeneousSum.transportHom a
    (spanPresentation X) (spanPresentation Y)
    (spanImageRealization D T X).toHomogeneousSum
    (spanImageRealization D T Y).toHomogeneousSum).symm f.hom)
  map_preimage f := by
    apply ObjectProperty.hom_ext
    exact (HomogeneousSum.transportHom a _ _ _ _).apply_symm_apply f.hom
  preimage_map f := by
    apply ObjectProperty.hom_ext
    exact (HomogeneousSum.transportHom a _ _ _ _).symm_apply_apply f.hom

end RMod.Classification
