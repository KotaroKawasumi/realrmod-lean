import Mathlib

/-! The braided tensor product of enrichments, with Mathlib's interchange map. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
universe u₁ u₂ v w
namespace RMod.EnrichedSupport

section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V]
  {C : Type u₁} [EnrichedCategory V C]

theorem id_comp (X Y : C) :
    eId V X ▷ _ ≫ eComp V X X Y = (λ_ _).hom := by
  simpa only [Category.comp_id] using (Iso.inv_comp_eq _).mp (e_id_comp V X Y)

theorem comp_id (X Y : C) :
    _ ◁ eId V Y ≫ eComp V X Y Y = (ρ_ _).hom := by
  simpa only [Category.comp_id] using (Iso.inv_comp_eq _).mp (e_comp_id V X Y)

theorem assoc (W X Y Z : C) :
    eComp V W X Y ▷ _ ≫ eComp V W Y Z =
      (α_ _ _ _).hom ≫ _ ◁ eComp V X Y Z ≫ eComp V W X Z :=
  (Iso.inv_comp_eq _).mp (e_assoc V W X Y Z)
end

/-- This is a constructor, not a global enrichment instance on ordinary products. -/
@[implicit_reducible] def productEnrichment (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
    (C : Type u₁) (D : Type u₂) [EnrichedCategory V C] [EnrichedCategory V D] :
    EnrichedCategory V (C × D) where
  Hom X Y := (X.1 ⟶[V] Y.1) ⊗ (X.2 ⟶[V] Y.2)
  id X := (λ_ (𝟙_ V)).inv ≫ (eId V X.1 ⊗ₘ eId V X.2)
  comp X Y Z := tensorμ _ _ _ _ ≫ (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2)
  id_comp X Y := by
    change (λ_ _).inv ≫ (((λ_ (𝟙_ V)).inv ≫
      (eId V X.1 ⊗ₘ eId V X.2)) ▷ _) ≫
      tensorμ _ _ _ _ ≫ (eComp V X.1 X.1 Y.1 ⊗ₘ eComp V X.2 X.2 Y.2) = _
    rw [comp_whiskerRight, Category.assoc, tensorμ_natural_left_assoc,
      tensorHom_comp_tensorHom, id_comp, id_comp,
      ← tensor_left_unitality, Iso.inv_hom_id]
  comp_id X Y := by
    change (ρ_ _).inv ≫ (_ ◁ ((λ_ (𝟙_ V)).inv ≫
      (eId V Y.1 ⊗ₘ eId V Y.2))) ≫
      tensorμ _ _ _ _ ≫ (eComp V X.1 Y.1 Y.1 ⊗ₘ eComp V X.2 Y.2 Y.2) = _
    rw [whiskerLeft_comp, Category.assoc, tensorμ_natural_right_assoc,
      tensorHom_comp_tensorHom, comp_id, comp_id,
      ← tensor_right_unitality, Iso.inv_hom_id]
  assoc W X Y Z := by
    change (α_ _ _ _).inv ≫
      ((tensorμ _ _ _ _ ≫ (eComp V W.1 X.1 Y.1 ⊗ₘ eComp V W.2 X.2 Y.2)) ▷ _) ≫
      tensorμ _ _ _ _ ≫ (eComp V W.1 Y.1 Z.1 ⊗ₘ eComp V W.2 Y.2 Z.2) =
      _ ◁ (tensorμ _ _ _ _ ≫ (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2)) ≫
      tensorμ _ _ _ _ ≫ (eComp V W.1 X.1 Z.1 ⊗ₘ eComp V W.2 X.2 Z.2)
    rw [comp_whiskerRight, Category.assoc, tensorμ_natural_left_assoc,
      tensorHom_comp_tensorHom, assoc, assoc]
    rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom,
      tensor_associativity_assoc, Iso.inv_hom_id_assoc]
    rw [whiskerLeft_comp, Category.assoc, tensorμ_natural_right_assoc,
      tensorHom_comp_tensorHom]

end RMod.EnrichedSupport
