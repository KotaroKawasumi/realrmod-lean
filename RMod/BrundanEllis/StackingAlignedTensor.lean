import RMod.BrundanEllis.StackingProductEven
import RMod.BrundanEllis.Surface
import RMod.Enriched.Compatibility

/-! Normalize the enriched tensor's object map without changing its specified
Hom operation. On pairs of even arrows it is the ordinary tensor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable (C : Type) [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalSuperCategory C]

def alignedSuperTensor : SuperFunctor (SuperTensorProduct C C) C :=
  RMod.alignedTensor SuperVec MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects

theorem alignedSuperTensor_map (X Y : Even C × Even C) :
    (alignedSuperTensor C).map (X.1, X.2) (Y.1, Y.2) =
      enrichedTensorMap MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        X.1 Y.1 X.2 Y.2 := by
  calc
    _ = RMod.enrichedTensorMap SuperVec MonoidalSuperCategory.tensor
        MonoidalSuperCategory.tensor_objects X.1 Y.1 X.2 Y.2 :=
      eq_of_heq (RMod.alignedTensor_map_heq SuperVec (MonoidalSuperCategory.tensor (C := C))
        MonoidalSuperCategory.tensor_objects (X.1, X.2) (Y.1, Y.2))
    _ = _ := by
      simp only [RMod.enrichedTensorMap, eqToHom_refl, Category.id_comp]
      rfl

theorem alignedSuperTensor_even {X Y : Even C × Even C} (f : X ⟶ Y) :
    (evenPairFunctor (alignedSuperTensor C)).map f = f.1 ⊗ₘ f.2 := by
  apply (eHomEquiv SuperVec).injective
  change (λ_ (𝟙_ SuperVec)).inv ≫
      (ForgetEnrichment.homTo SuperVec f.1 ⊗ₘ ForgetEnrichment.homTo SuperVec f.2) ≫
      (alignedSuperTensor C).map (X.1, X.2) (Y.1, Y.2) =
    ForgetEnrichment.homTo SuperVec (f.1 ⊗ₘ f.2)
  rw [alignedSuperTensor_map]
  exact MonoidalSuperCategory.tensor_even f.1 f.2

end RMod.BrundanEllis.Stacking
