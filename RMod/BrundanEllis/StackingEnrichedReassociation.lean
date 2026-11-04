import RMod.Enriched.Surface

/-! The inverse reassociation functor uses the inverse of the same ambient
associator. Its laws follow by cancelling the already proved forward maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
universe u₁ u₂ u₃ v w
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  (A : Type u₁) (B : Type u₂) (C : Type u₃)
  [EnrichedCategory V A] [EnrichedCategory V B] [EnrichedCategory V C]

def enrichedReassociateInv :
    EnrichedFunctor V (EnrichedTensorProduct V A (EnrichedTensorProduct V B C))
      (EnrichedTensorProduct V (EnrichedTensorProduct V A B) C) where
  obj X := EnrichedTensorProduct.of V (EnrichedTensorProduct.of V X.1 X.2.1) X.2.2
  map X Y := (α_ (X.1 ⟶[V] Y.1) (X.2.1 ⟶[V] Y.2.1) (X.2.2 ⟶[V] Y.2.2)).inv
  map_id X := by
    apply (Iso.comp_inv_eq (α_ _ _ _)).mpr
    exact ((RMod.reassociate V A B C).map_id
      (EnrichedTensorProduct.of V (EnrichedTensorProduct.of V X.1 X.2.1) X.2.2)).symm
  map_comp X Y Z := by
    apply (Iso.comp_inv_eq (α_ _ _ _)).mpr
    have h := (RMod.reassociate V A B C).map_comp
      (EnrichedTensorProduct.of V (EnrichedTensorProduct.of V X.1 X.2.1) X.2.2)
      (EnrichedTensorProduct.of V (EnrichedTensorProduct.of V Y.1 Y.2.1) Y.2.2)
      (EnrichedTensorProduct.of V (EnrichedTensorProduct.of V Z.1 Z.2.1) Z.2.2)
    change (tensorμ _ _ _ _ ≫
      ((tensorμ _ _ _ _ ≫ (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2.1 Y.2.1 Z.2.1)) ⊗ₘ
        eComp V X.2.2 Y.2.2 Z.2.2)) ≫ (α_ _ _ _).hom =
      ((α_ _ _ _).hom ⊗ₘ (α_ _ _ _).hom) ≫ tensorμ _ _ _ _ ≫
        (eComp V X.1 Y.1 Z.1 ⊗ₘ
          (tensorμ _ _ _ _ ≫ (eComp V X.2.1 Y.2.1 Z.2.1 ⊗ₘ eComp V X.2.2 Y.2.2 Z.2.2))) at h
    change tensorμ _ _ _ _ ≫ (eComp V X.1 Y.1 Z.1 ⊗ₘ
        (tensorμ _ _ _ _ ≫ (eComp V X.2.1 Y.2.1 Z.2.1 ⊗ₘ eComp V X.2.2 Y.2.2 Z.2.2))) =
      (((α_ _ _ _).inv ⊗ₘ (α_ _ _ _).inv) ≫
        (tensorμ _ _ _ _ ≫ ((tensorμ _ _ _ _ ≫
          (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2.1 Y.2.1 Z.2.1)) ⊗ₘ
            eComp V X.2.2 Y.2.2 Z.2.2))) ≫ (α_ _ _ _).hom
    rw [Category.assoc, h]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id,
      tensorHom_id, id_whiskerRight, Category.id_comp]

end RMod.BrundanEllis.Stacking
