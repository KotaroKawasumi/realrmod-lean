import RMod.Hierarchy.Abstract.SuperTensorProduct

/-!
# Laws of the enriched tensor product

Mathlib's monoidal tensor functor supplies the unit and associativity
coherence for the product enrichment.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
namespace RMod.Legacy

theorem enriched_id_comp (C : Supercategory) (X Y : C.data.Obj) :
    C.data.id X ▷ _ ≫ C.data.comp X X Y = (λ_ _).hom := by
  simpa only [comp_id] using (Iso.inv_comp_eq _).mp (C.laws.id_comp X Y)

theorem enriched_comp_id (C : Supercategory) (X Y : C.data.Obj) :
    _ ◁ C.data.id Y ≫ C.data.comp X Y Y = (ρ_ _).hom := by
  simpa only [comp_id] using (Iso.inv_comp_eq _).mp (C.laws.comp_id X Y)

theorem enriched_assoc (C : Supercategory) (W X Y Z : C.data.Obj) :
    C.data.comp W X Y ▷ _ ≫ C.data.comp W Y Z =
      (α_ _ _ _).hom ≫ _ ◁ C.data.comp X Y Z ≫ C.data.comp W X Z :=
  (Iso.inv_comp_eq _).mp (C.laws.assoc W X Y Z)

def superTensorProductLaws (C D : Supercategory) :
    SupercategoryLaws (superTensorProductData C.data D.data) where
  id_comp := by
    intro X Y
    change C.data.Obj × D.data.Obj at X Y
    change (λ_ _).inv ≫ (((λ_ (𝟙_ SuperVec)).inv ≫
      (C.data.id X.1 ⊗ₘ D.data.id X.2)) ▷ _) ≫
      tensorμ _ _ _ _ ≫ (C.data.comp X.1 X.1 Y.1 ⊗ₘ D.data.comp X.2 X.2 Y.2) = _
    rw [comp_whiskerRight, assoc, tensorμ_natural_left_assoc,
      tensorHom_comp_tensorHom, enriched_id_comp, enriched_id_comp,
      ← tensor_left_unitality, Iso.inv_hom_id]
    rfl
  comp_id := by
    intro X Y
    change C.data.Obj × D.data.Obj at X Y
    change (ρ_ _).inv ≫ (_ ◁ ((λ_ (𝟙_ SuperVec)).inv ≫
      (C.data.id Y.1 ⊗ₘ D.data.id Y.2))) ≫
      tensorμ _ _ _ _ ≫ (C.data.comp X.1 Y.1 Y.1 ⊗ₘ D.data.comp X.2 Y.2 Y.2) = _
    rw [whiskerLeft_comp, assoc, tensorμ_natural_right_assoc,
      tensorHom_comp_tensorHom, enriched_comp_id, enriched_comp_id,
      ← tensor_right_unitality, Iso.inv_hom_id]
    rfl
  assoc := by
    intro W X Y Z
    change C.data.Obj × D.data.Obj at W X Y Z
    change (α_ _ _ _).inv ≫
      ((tensorμ _ _ _ _ ≫ (C.data.comp W.1 X.1 Y.1 ⊗ₘ D.data.comp W.2 X.2 Y.2)) ▷ _) ≫
      tensorμ _ _ _ _ ≫ (C.data.comp W.1 Y.1 Z.1 ⊗ₘ D.data.comp W.2 Y.2 Z.2) =
    _ ◁ (tensorμ _ _ _ _ ≫ (C.data.comp X.1 Y.1 Z.1 ⊗ₘ D.data.comp X.2 Y.2 Z.2)) ≫
      tensorμ _ _ _ _ ≫ (C.data.comp W.1 X.1 Z.1 ⊗ₘ D.data.comp W.2 X.2 Z.2)
    rw [comp_whiskerRight, assoc, tensorμ_natural_left_assoc,
      tensorHom_comp_tensorHom, enriched_assoc, enriched_assoc]
    rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom,
      tensor_associativity_assoc, Iso.inv_hom_id_assoc]
    rw [whiskerLeft_comp, assoc, tensorμ_natural_right_assoc,
      tensorHom_comp_tensorHom]

def SuperTensorProduct (C D : Supercategory) : Supercategory :=
  ⟨superTensorProductData C.data D.data, superTensorProductLaws C D⟩

end RMod.Legacy
