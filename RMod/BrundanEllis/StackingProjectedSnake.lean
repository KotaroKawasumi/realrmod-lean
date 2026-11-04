import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! Inserting an idempotent in both ends of a snake diagram gives the
original snake restricted by that idempotent. These ordinary monoidal
calculations are independent of the choice of enrichment. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C : Type} [Category C] [MonoidalCategory C]

theorem projected_forward_snake {X Y : C} (p : X ⟶ X) (hp : p ≫ p = p)
    (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C) :
    ((η ≫ p ▷ Y) ⊗ₘ p) ≫ (α_ X Y X).hom ≫ (p ⊗ₘ (Y ◁ p ≫ ε)) =
      (𝟙 (𝟙_ C) ⊗ₘ p) ≫ (η ⊗ₘ 𝟙 X) ≫ (α_ X Y X).hom ≫
        (𝟙 X ⊗ₘ ε) ≫ (p ⊗ₘ 𝟙 (𝟙_ C)) := by
  have hf : ((η ≫ p ▷ Y) ⊗ₘ p) = (η ⊗ₘ p) ≫ ((p ▷ Y) ▷ X) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  rw [hf, assoc, associator_naturality_left_assoc]
  simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id, hp, tensorHom_comp_tensorHom]
  have hg : p ⊗ₘ ((𝟙 Y ⊗ₘ p) ≫ ε) = (X ◁ (Y ◁ p)) ≫ (p ⊗ₘ ε) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [hg, ← assoc (α_ X Y X).hom, ← associator_naturality_right]
  simp only [assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, id_tensorHom_id,
    Category.comp_id, hp]

/-- The same restriction identity for the opposite snake convention. -/
theorem projected_backward_snake {X Y : C} (q : Y ⟶ Y) (hq : q ≫ q = q)
    (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C) :
    (q ⊗ₘ (η ≫ X ◁ q)) ≫ (α_ Y X Y).inv ≫ ((q ▷ X ≫ ε) ⊗ₘ q) =
      (q ⊗ₘ 𝟙 (𝟙_ C)) ≫ (𝟙 Y ⊗ₘ η) ≫ (α_ Y X Y).inv ≫
        (ε ⊗ₘ 𝟙 Y) ≫ (𝟙 (𝟙_ C) ⊗ₘ q) := by
  have hf : (q ⊗ₘ (η ≫ X ◁ q)) = (q ⊗ₘ η) ≫ (Y ◁ (X ◁ q)) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  rw [hf, assoc, associator_inv_naturality_right_assoc]
  simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id, hq, tensorHom_comp_tensorHom]
  have hg : ((q ⊗ₘ 𝟙 X) ≫ ε) ⊗ₘ q = ((q ▷ X) ▷ Y) ≫ (ε ⊗ₘ q) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  rw [hg, ← assoc (α_ Y X Y).inv, ← associator_inv_naturality_left]
  simp only [assoc, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, id_tensorHom_id,
    Category.comp_id, hq]

end RMod.BrundanEllis.Stacking
