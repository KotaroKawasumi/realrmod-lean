import RMod.BrundanEllis.StackingEvenNaturality

/-! Ordinary even tensor points and threefold naturality. These generic
coherence identities evaluate enriched tensor diagrams at degree-zero points. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {V : Type*} [Category* V] [MonoidalCategory V]

@[reassoc] theorem even_left_tensor {H I T : V}
    (f : 𝟙_ V ⟶ H) (e : 𝟙_ V ⟶ I) (t : I ⊗ H ⟶ T) :
    f ≫ (λ_ H).inv ≫ (e ⊗ₘ 𝟙 H) ≫ t = (λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ f) ≫ t := by
  simp only [tensorHom_def', comp_whiskerRight, whiskerLeft_comp, assoc]
  monoidal

@[reassoc] theorem even_right_tensor {H I T : V}
    (f : 𝟙_ V ⟶ H) (e : 𝟙_ V ⟶ I) (t : H ⊗ I ⟶ T) :
    f ≫ (ρ_ H).inv ≫ (𝟙 H ⊗ₘ e) ≫ t = (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ e) ≫ t := by
  simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp, assoc]
  monoidal

/-- Evaluate a threefold Hom naturality diagram at three even points. -/
theorem even_triple_naturality {H K L P Q R S T : V}
    (f : 𝟙_ V ⟶ H) (g : 𝟙_ V ⟶ K) (h : 𝟙_ V ⟶ L)
    (p : H ⊗ K ⟶ P) (q : P ⊗ L ⟶ R)
    (r : K ⊗ L ⟶ Q) (s : H ⊗ Q ⟶ S)
    (a : R ⟶ T) (b : S ⟶ T)
    (hn : (p ⊗ₘ 𝟙 L) ≫ q ≫ a =
      (α_ H K L).hom ≫ (𝟙 H ⊗ₘ r) ≫ s ≫ b) :
    (λ_ (𝟙_ V)).inv ≫ (((λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g) ≫ p) ⊗ₘ h) ≫ q ≫ a =
      (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (g ⊗ₘ h) ≫ r)) ≫ s ≫ b := by
  calc
    _ = (λ_ (𝟙_ V)).inv ≫ (((λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g)) ⊗ₘ h) ≫
        (p ⊗ₘ 𝟙 L) ≫ q ≫ a := by
      simp only [tensorHom_comp_tensorHom_assoc, comp_id, assoc]
    _ = _ := by
      rw [hn]
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp, assoc]
      monoidal

end RMod.BrundanEllis.Stacking
