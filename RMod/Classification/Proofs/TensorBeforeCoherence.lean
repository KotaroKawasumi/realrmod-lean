import RMod.Classification.Instances.TensorIsoBeforeCoherence

/-! # Bifunctor identities used to cancel tensor comparisons -/

set_option autoImplicit false
universe u v

namespace RMod.Classification.TensorStructuralLaws

open CategoryTheory CategoryTheory.MonoidalCategory

variable {D : Type u} [Category.{v} D] [MonoidalCategoryStruct D]
  (hD : TensorStructuralLaws D)

include hD

@[reassoc]
theorem tensor_comp_reverse {X₁ X₂ X₃ Y₁ Y₂ Y₃ : D}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : Y₁ ⟶ Y₂) (k : Y₂ ⟶ Y₃) :
    (f ⊗ₘ h) ≫ (g ⊗ₘ k) = (f ≫ g) ⊗ₘ (h ≫ k) :=
  (hD.tensor_comp f g h k).symm

end RMod.Classification.TensorStructuralLaws
