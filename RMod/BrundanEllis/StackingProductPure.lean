import RMod.BrundanEllis.StackingProductWhisker

/-! The pairing of even categories preserves the componentwise tensor on
pure pairs of even maps. This supplies the ordinary coherence diagrams. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {A B : Type} [SuperCategory A] [SuperCategory B]
  [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]

@[reassoc] private theorem unit_interchange :
    (λ_ (𝟙_ SuperVec)).inv ≫ ((λ_ (𝟙_ SuperVec)).inv ⊗ₘ (λ_ (𝟙_ SuperVec)).inv) ≫
      tensorμ (𝟙_ SuperVec) (𝟙_ SuperVec) (𝟙_ SuperVec) (𝟙_ SuperVec) =
    (λ_ (𝟙_ SuperVec)).inv ≫ ((λ_ (𝟙_ SuperVec)).inv ⊗ₘ (λ_ (𝟙_ SuperVec)).inv) := by
  simp only [tensorμ, braiding_tensorUnit_left]
  monoidal

theorem product_tensor_homTo {X X' Y Y' : Even (SuperTensorProduct A B)}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ForgetEnrichment.homTo SuperVec (f ⊗ₘ g) =
      (λ_ (𝟙_ SuperVec)).inv ≫
        (ForgetEnrichment.homTo SuperVec f ⊗ₘ ForgetEnrichment.homTo SuperVec g) ≫
          (productTensor A B).map (X, Y) (X', Y') := rfl

/-- The pairing's object formula is reduced before using monoidal naturality. -/
theorem productTensor_even_map (X X' Y Y' : Even A × Even B) :
    (productTensor A B).map ((productPair A B).obj X, (productPair A B).obj Y)
      ((productPair A B).obj X', (productPair A B).obj Y') =
    tensorμ (SHom A (ForgetEnrichment.to SuperVec X.1) (ForgetEnrichment.to SuperVec X'.1))
      (SHom B (ForgetEnrichment.to SuperVec X.2) (ForgetEnrichment.to SuperVec X'.2))
      (SHom A (ForgetEnrichment.to SuperVec Y.1) (ForgetEnrichment.to SuperVec Y'.1))
      (SHom B (ForgetEnrichment.to SuperVec Y.2) (ForgetEnrichment.to SuperVec Y'.2)) ≫
      (enrichedTensorMap (C := A) MonoidalSuperCategory.tensor
        MonoidalSuperCategory.tensor_objects X.1 X'.1 Y.1 Y'.1 ⊗ₘ
       enrichedTensorMap (C := B) MonoidalSuperCategory.tensor
        MonoidalSuperCategory.tensor_objects X.2 X'.2 Y.2 Y'.2) :=
  productTensor_map A B _ _

@[simp] theorem productPair_tensor {X X' Y Y' : Even A × Even B}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (productPair A B).map f ⊗ₘ (productPair A B).map g =
      (productPair A B).map (f ⊗ₘ g) := by
  apply_fun ForgetEnrichment.homTo SuperVec
  · rw [product_tensor_homTo, productPair_map_homTo, productPair_map_homTo,
      productPair_map_homTo, productTensor_even_map]
    simp only [← tensorHom_comp_tensorHom_assoc]
    rw [tensorμ_natural_assoc, unit_interchange_assoc]
    simp only [tensorHom_comp_tensorHom]
    rw [MonoidalSuperCategory.tensor_even, MonoidalSuperCategory.tensor_even]
    rfl
  · intro f g h
    exact congrArg (ForgetEnrichment.homOf SuperVec) h

end RMod.BrundanEllis.Stacking
