import RMod.BrundanEllis.StackingTensorUnit

/-! Tensoring two naturality squares and inserting braided interchange.
The hypotheses are component Hom identities, not coherence assumptions on
the product category. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {V : Type*} [Category* V] [MonoidalCategory V] [BraidedCategory V]

theorem tensor_assoc_naturality
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ P₁ P₂ Q₁ Q₂ L₁ L₂ R₁ R₂ T₁ T₂ : V}
    (p₁ : X₁ ⊗ Y₁ ⟶ P₁) (p₂ : X₂ ⊗ Y₂ ⟶ P₂)
    (q₁ : P₁ ⊗ Z₁ ⟶ L₁) (q₂ : P₂ ⊗ Z₂ ⟶ L₂)
    (r₁ : Y₁ ⊗ Z₁ ⟶ Q₁) (r₂ : Y₂ ⊗ Z₂ ⟶ Q₂)
    (s₁ : X₁ ⊗ Q₁ ⟶ R₁) (s₂ : X₂ ⊗ Q₂ ⟶ R₂)
    (l₁ : L₁ ⟶ T₁) (l₂ : L₂ ⟶ T₂)
    (k₁ : R₁ ⟶ T₁) (k₂ : R₂ ⟶ T₂)
    (h₁ : p₁ ▷ Z₁ ≫ q₁ ≫ l₁ =
      (α_ X₁ Y₁ Z₁).hom ≫ X₁ ◁ r₁ ≫ s₁ ≫ k₁)
    (h₂ : p₂ ▷ Z₂ ≫ q₂ ≫ l₂ =
      (α_ X₂ Y₂ Z₂).hom ≫ X₂ ◁ r₂ ≫ s₂ ≫ k₂) :
    (tensorμ X₁ X₂ Y₁ Y₂ ≫ (p₁ ⊗ₘ p₂)) ▷ (Z₁ ⊗ Z₂) ≫
        tensorμ P₁ P₂ Z₁ Z₂ ≫ (q₁ ⊗ₘ q₂) ≫ (l₁ ⊗ₘ l₂) =
      (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
        (X₁ ⊗ X₂) ◁ (tensorμ Y₁ Y₂ Z₁ Z₂ ≫ (r₁ ⊗ₘ r₂)) ≫
        tensorμ X₁ X₂ Q₁ Q₂ ≫ (s₁ ⊗ₘ s₂) ≫ (k₁ ⊗ₘ k₂) := by
  rw [comp_whiskerRight, assoc, tensorμ_natural_left_assoc]
  simp only [tensorHom_comp_tensorHom]
  rw [h₁, h₂]
  simp only [← tensorHom_comp_tensorHom]
  rw [tensor_associativity_assoc]
  rw [whiskerLeft_comp, assoc, tensorμ_natural_right_assoc]

/-- Left-unit naturality tensors componentwise, including the unit comparison. -/
theorem tensor_left_naturality {I₁ I₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ : V}
    (e₁ : 𝟙_ V ⟶ I₁) (e₂ : 𝟙_ V ⟶ I₂)
    (t₁ : I₁ ⊗ X₁ ⟶ Y₁) (t₂ : I₂ ⊗ X₂ ⟶ Y₂)
    (l₁ : Y₁ ⟶ Z₁) (l₂ : Y₂ ⟶ Z₂)
    (k₁ : X₁ ⟶ Z₁) (k₂ : X₂ ⟶ Z₂)
    (h₁ : (λ_ X₁).inv ≫ e₁ ▷ X₁ ≫ t₁ ≫ l₁ = k₁)
    (h₂ : (λ_ X₂).inv ≫ e₂ ▷ X₂ ≫ t₂ ≫ l₂ = k₂) :
    (λ_ (X₁ ⊗ X₂)).inv ≫ ((λ_ (𝟙_ V)).inv ≫ (e₁ ⊗ₘ e₂)) ▷ (X₁ ⊗ X₂) ≫
      tensorμ I₁ I₂ X₁ X₂ ≫ (t₁ ⊗ₘ t₂) ≫ (l₁ ⊗ₘ l₂) = k₁ ⊗ₘ k₂ := by
  rw [comp_whiskerRight, assoc, tensorμ_natural_left_assoc,
    tensor_left_unitality_inv_assoc]
  simp only [tensorHom_comp_tensorHom, h₁, h₂]

/-- Right-unit naturality is compatible with the same braided unit comparison. -/
theorem tensor_right_naturality {I₁ I₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ : V}
    (e₁ : 𝟙_ V ⟶ I₁) (e₂ : 𝟙_ V ⟶ I₂)
    (t₁ : X₁ ⊗ I₁ ⟶ Y₁) (t₂ : X₂ ⊗ I₂ ⟶ Y₂)
    (l₁ : Y₁ ⟶ Z₁) (l₂ : Y₂ ⟶ Z₂)
    (k₁ : X₁ ⟶ Z₁) (k₂ : X₂ ⟶ Z₂)
    (h₁ : (ρ_ X₁).inv ≫ X₁ ◁ e₁ ≫ t₁ ≫ l₁ = k₁)
    (h₂ : (ρ_ X₂).inv ≫ X₂ ◁ e₂ ≫ t₂ ≫ l₂ = k₂) :
    (ρ_ (X₁ ⊗ X₂)).inv ≫ (X₁ ⊗ X₂) ◁ ((λ_ (𝟙_ V)).inv ≫ (e₁ ⊗ₘ e₂)) ≫
      tensorμ X₁ X₂ I₁ I₂ ≫ (t₁ ⊗ₘ t₂) ≫ (l₁ ⊗ₘ l₂) = k₁ ⊗ₘ k₂ := by
  rw [whiskerLeft_comp, assoc, tensorμ_natural_right_assoc,
    tensor_right_unitality_inv_assoc]
  simp only [tensorHom_comp_tensorHom, h₁, h₂]

end RMod.BrundanEllis.Stacking
