import RMod.Classification.Instances.SimpleCornerMap
import RMod.Classification.Proofs.SimpleRetractCoordinates

/-!
# Algebra and inverse laws for the transported corner map

Expanding the compressed target map recovers the ambient algebra image
because that image is supported by the transported projector. This
identity proves both inverse identities and preservation of the unit
and composition, without choosing a basis of either corner algebra.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

theorem endAlgEquiv_map_comp (C D : WeaklyPointedSuperfusion.{0, 0})
    {X : LinearCategory C} {Y : LinearCategory D} (φ : End X ≃ₐ[ℝ] End Y) (f g : End X) :
    φ (C.data.comp f g) = D.data.comp (φ f) (φ g) := φ.map_mul g f

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {X : LinearCategory C} {Y : LinearCategory D}
  (d : SimpleRetract C X) (t : SimpleRetract D Y) (φ : End X ≃ₐ[ℝ] End Y)
  (hproj : SimpleRetract.projectorData t.data = φ (SimpleRetract.projectorData d.data))

include hproj

theorem expand_simpleCornerMap (f : @End (LinearCategory C) _ d.data.object) :
    SimpleRetract.expand D t.data (simpleCornerMap C D d.data t.data φ f) =
      φ (SimpleRetract.expand C d.data f) := by
  change SimpleRetract.expand D t.data
    (SimpleRetract.compress D t.data (φ (SimpleRetract.expand C d.data f))) = _
  rw [t.expand_compress, hproj]
  rw [← endAlgEquiv_map_comp C D φ, ← endAlgEquiv_map_comp C D φ,
    d.expand_projector, d.projector_expand]

theorem simpleCornerMap_inverse (f : @End (LinearCategory C) _ d.data.object) :
    simpleCornerMap D C t.data d.data φ.symm (simpleCornerMap C D d.data t.data φ f) = f := by
  change SimpleRetract.compress C d.data
    (φ.symm (SimpleRetract.expand D t.data (simpleCornerMap C D d.data t.data φ f))) = f
  rw [expand_simpleCornerMap d t φ hproj, AlgEquiv.symm_apply_apply, d.compress_expand]

theorem simpleCornerMap_id : simpleCornerMap C D d.data t.data φ (𝟙 _) = 𝟙 _ := by
  apply t.expand_injective
  rw [expand_simpleCornerMap d t φ hproj, d.expand_id, t.expand_id]
  exact hproj.symm

theorem simpleCornerMap_comp (f g : @End (LinearCategory C) _ d.data.object) :
    simpleCornerMap C D d.data t.data φ (f ≫ g) =
      simpleCornerMap C D d.data t.data φ f ≫ simpleCornerMap C D d.data t.data φ g := by
  apply t.expand_injective
  rw [expand_simpleCornerMap d t φ hproj, d.expand_comp, t.expand_comp]
  rw [expand_simpleCornerMap d t φ hproj, expand_simpleCornerMap d t φ hproj]
  exact endAlgEquiv_map_comp C D φ _ _

omit hproj in
theorem simpleCornerMap_grade
    (hφ : ∀ {a : ZMod 2} {f : End X}, C.data.IsHomogeneous a f → D.data.IsHomogeneous a (φ f))
    {a : ZMod 2} (f : @End (LinearCategory C) _ d.data.object) (hf : C.data.IsHomogeneous a f) :
    D.data.IsHomogeneous a (simpleCornerMap C D d.data t.data φ f) := by
  have hex := C.laws.comp_grade _ _ d.laws.projection_even
    (C.laws.comp_grade _ _ hf d.laws.inclusion_even)
  simp only [zero_add, add_zero] at hex
  have hmap := hφ hex
  have h := D.laws.comp_grade _ _ t.laws.inclusion_even
    (D.laws.comp_grade _ _ hmap t.laws.projection_even)
  simp only [zero_add, add_zero] at h
  exact h

end RMod.Classification
