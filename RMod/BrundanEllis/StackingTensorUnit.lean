import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! Inverse unit coherence for the braided tensor functor. These identities
allow componentwise even maps to act on every enriched Hom degree. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {V : Type*} [Category* V] [MonoidalCategory V] [BraidedCategory V]

@[reassoc] theorem tensor_left_unitality_inv (X Y : V) :
    (λ_ (X ⊗ Y)).inv ≫ (λ_ (𝟙_ V)).inv ▷ (X ⊗ Y) ≫
      tensorμ (𝟙_ V) (𝟙_ V) X Y = (λ_ X).inv ⊗ₘ (λ_ Y).inv := by
  apply (cancel_mono ((λ_ X).hom ⊗ₘ (λ_ Y).hom)).1
  simp only [assoc, ← tensor_left_unitality, Iso.inv_hom_id,
    tensorHom_comp_tensorHom, tensorHom_id, id_whiskerRight]

@[reassoc] theorem tensor_right_unitality_inv (X Y : V) :
    (ρ_ (X ⊗ Y)).inv ≫ (X ⊗ Y) ◁ (λ_ (𝟙_ V)).inv ≫
      tensorμ X Y (𝟙_ V) (𝟙_ V) = (ρ_ X).inv ⊗ₘ (ρ_ Y).inv := by
  apply (cancel_mono ((ρ_ X).hom ⊗ₘ (ρ_ Y).hom)).1
  simp only [assoc, ← tensor_right_unitality, Iso.inv_hom_id,
    tensorHom_comp_tensorHom, tensorHom_id, id_whiskerRight]

end RMod.BrundanEllis.Stacking
