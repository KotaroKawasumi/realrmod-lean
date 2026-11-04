import RMod.BrundanEllis.StackingProductStructure
import RMod.BrundanEllis.StackingTensorUnit

/-! Whiskering by a pair of even maps factors on the full Hom objects.
Thus the identities below include the odd--odd summand of even Hom. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {A B : Type} [SuperCategory A] [SuperCategory B]

@[simp] theorem productPair_map_homTo {X Y : Even A × Even B} (f : X ⟶ Y) :
    ForgetEnrichment.homTo SuperVec ((productPair A B).map f) =
      (λ_ (𝟙_ SuperVec)).inv ≫
        (ForgetEnrichment.homTo SuperVec f.1 ⊗ₘ ForgetEnrichment.homTo SuperVec f.2) := by
  rfl

@[simp] theorem product_whisker_left (X : Even A × Even B)
    {Y Z : Even A × Even B} (f : Y ⟶ Z) :
    eHomWhiskerLeft SuperVec (C := Even (SuperTensorProduct A B))
      ((productPair A B).obj X) ((productPair A B).map f) =
    eHomWhiskerLeft SuperVec X.1 f.1 ⊗ₘ eHomWhiskerLeft SuperVec X.2 f.2 := by
  change (ρ_ _).inv ≫ _ ◁
    (ForgetEnrichment.homTo SuperVec ((productPair A B).map f)) ≫ _ = _
  rw [productPair_map_homTo]
  change (ρ_ _).inv ≫ _ ◁ ((λ_ (𝟙_ SuperVec)).inv ≫
      (ForgetEnrichment.homTo SuperVec f.1 ⊗ₘ ForgetEnrichment.homTo SuperVec f.2)) ≫
      tensorμ _ _ _ _ ≫ (eComp SuperVec X.1 Y.1 Z.1 ⊗ₘ eComp SuperVec X.2 Y.2 Z.2) = _
  rw [whiskerLeft_comp, assoc, tensorμ_natural_right_assoc,
    tensor_right_unitality_inv_assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom]
  rfl

@[simp] theorem product_whisker_right {X Y : Even A × Even B}
    (f : X ⟶ Y) (Z : Even A × Even B) :
    eHomWhiskerRight SuperVec (C := Even (SuperTensorProduct A B))
      ((productPair A B).map f) ((productPair A B).obj Z) =
    eHomWhiskerRight SuperVec f.1 Z.1 ⊗ₘ eHomWhiskerRight SuperVec f.2 Z.2 := by
  change (λ_ _).inv ≫
    (ForgetEnrichment.homTo SuperVec ((productPair A B).map f)) ▷ _ ≫ _ = _
  rw [productPair_map_homTo]
  change (λ_ _).inv ≫ ((λ_ (𝟙_ SuperVec)).inv ≫
      (ForgetEnrichment.homTo SuperVec f.1 ⊗ₘ ForgetEnrichment.homTo SuperVec f.2)) ▷ _ ≫
      tensorμ _ _ _ _ ≫ (eComp SuperVec X.1 Y.1 Z.1 ⊗ₘ eComp SuperVec X.2 Y.2 Z.2) = _
  rw [comp_whiskerRight, assoc, tensorμ_natural_left_assoc,
    tensor_left_unitality_inv_assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom]
  rfl

end RMod.BrundanEllis.Stacking
