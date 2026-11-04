import RMod.BrundanEllis.StackingHullSemisimple
import RMod.BrundanEllis.StackingParity
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-! Restriction of the existing tensor to a tensor-closed completion. The
ordinary operations are the ambient operations, and the faithful inclusion
reflects their coherence. The additional closure assumptions here concern an
arbitrary generating family; they must be proved for the diagonal family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
variable (C : WeaklyPointedFusionPiSuperCat) {I : Type} (Z : I → Even C)

/-- An ambient even isomorphism between members of the hull is already an
isomorphism in the inherited even category. -/
def hullIso {X Y : Even (HullCategory C Z)} (e : X.obj ≅ Y.obj) : X ≅ Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

variable [ObjectProperty.IsMonoidal (AddPiHull C Z)]

/-- The unit and tensor objects carry only their proved membership in the hull. -/
instance hullMonoidalStruct : MonoidalCategoryStruct (Even (HullCategory C Z)) where
  tensorObj X Y := evenObj _ ⟨X.obj ⊗ Y.obj, ObjectProperty.prop_tensor X.property Y.property⟩
  whiskerLeft X _ _ f := X.obj ◁ f
  whiskerRight f Y := whiskerRight (C := Even C) f Y.obj
  tensorHom f g := tensorHom (C := Even C) f g
  tensorUnit := evenObj _ ⟨𝟙_ (Even C), ObjectProperty.prop_unit (AddPiHull C Z)⟩
  associator X Y W := hullIso C Z (α_ X.obj Y.obj W.obj)
  leftUnitor X := hullIso C Z (λ_ X.obj)
  rightUnitor X := hullIso C Z (ρ_ X.obj)

/-- The inclusion preserves each of the displayed operations. -/
def hullInducingData : Monoidal.InducingFunctorData (hullInclusion C Z).forget where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq X {Y₁ Y₂} f := by
    dsimp [hullInclusion, EnrichedFunctor.forget, ForgetEnrichment.homOf,
      ForgetEnrichment.homTo]
    change (X.obj ◁ (f : Y₁.obj ⟶ Y₂.obj)) = 𝟙 _ ≫ (X.obj ◁ f) ≫ 𝟙 _
    simp
  whiskerRight_eq {X₁ X₂} f Y := by
    dsimp [hullInclusion, EnrichedFunctor.forget, ForgetEnrichment.homOf,
      ForgetEnrichment.homTo]
    change whiskerRight (C := Even C) f Y.obj =
      𝟙 _ ≫ whiskerRight (C := Even C) f Y.obj ≫ 𝟙 _
    simp
  tensorHom_eq {X₁ Y₁ X₂ Y₂} f g := by
    dsimp [hullInclusion, EnrichedFunctor.forget, ForgetEnrichment.homOf,
      ForgetEnrichment.homTo]
    change ((f : X₁.obj ⟶ Y₁.obj) ⊗ₘ (g : X₂.obj ⟶ Y₂.obj)) =
      𝟙 _ ≫ (f ⊗ₘ g) ≫ 𝟙 _
    simp
  associator_eq X Y W := by
    dsimp [hullInclusion, EnrichedFunctor.forget, ForgetEnrichment.homOf,
      ForgetEnrichment.homTo]
    change (α_ X.obj Y.obj W.obj).hom =
      (𝟙 _ ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫ (α_ X.obj Y.obj W.obj).hom ≫
        ((𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _)
    simp
  leftUnitor_eq X := by
    dsimp [hullInclusion, EnrichedFunctor.forget, ForgetEnrichment.homOf,
      ForgetEnrichment.homTo]
    change (λ_ X.obj).hom = (𝟙 _ ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫ (λ_ X.obj).hom
    simp
  rightUnitor_eq X := by
    dsimp [hullInclusion, EnrichedFunctor.forget, ForgetEnrichment.homOf,
      ForgetEnrichment.homTo]
    change (ρ_ X.obj).hom = (𝟙 _ ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫ (ρ_ X.obj).hom
    simp

instance hullMonoidal : MonoidalCategory (Even (HullCategory C Z)) :=
  Monoidal.induced (hullInclusion C Z).forget (hullInducingData C Z)

/-- Its strong monoidal comparison maps are the actual identity maps. -/
def hullInclusionMonoidal : (hullInclusion C Z).forget.CoreMonoidal :=
  Monoidal.fromInducedCoreMonoidal (hullInclusion C Z).forget (hullInducingData C Z)

end RMod.BrundanEllis
