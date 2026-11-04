import RMod.BrundanEllis.Foundation

/-! Graded full faithfulness gives an actual inverse on even morphisms.
This adapter lets the ordinary idempotent-completion constructions use the
already established homogeneous Hom isomorphisms. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))

/-- Assemble the homogeneous linear equivalences into an isomorphism of Hom objects. -/
def superHomIso (X Y : C) : SHom C X Y ≅ SHom D (F.obj X) (F.obj Y) where
  hom := F.map X Y
  inv a := ModuleCat.ofHom (LinearEquiv.ofBijective (F.map X Y a).hom (hF X Y a)).symm.toLinearMap
  hom_inv_id := by
    funext a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (LinearEquiv.ofBijective (F.map X Y a).hom (hF X Y a)).symm_apply_apply x
  inv_hom_id := by
    funext a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (LinearEquiv.ofBijective (F.map X Y a).hom (hF X Y a)).apply_symm_apply x

/-- Postcomposition with the Hom isomorphism is bijective on even points. -/
def forgetFullyFaithful : F.forget.FullyFaithful where
  preimage {X Y} f := ForgetEnrichment.homOf SuperVec
    (ForgetEnrichment.homTo SuperVec f ≫ (superHomIso F hF X Y).inv)
  map_preimage {X Y} f := by
    change (ForgetEnrichment.homTo SuperVec f ≫ (superHomIso F hF X Y).inv) ≫
      (superHomIso F hF X Y).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  preimage_map {X Y} f := by
    change (ForgetEnrichment.homTo SuperVec f ≫ (superHomIso F hF X Y).hom) ≫
      (superHomIso F hF X Y).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl

end RMod.BrundanEllis.Stacking
