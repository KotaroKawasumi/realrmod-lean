import RMod.Enriched.FullNaturality
import RMod.Statement.MonoidalBridge

/-! The established total-morphism coherence laws imply the full enriched
naturality required by the new statement surface. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.EnrichedBridge
open Regression EnrichedSupport

variable (C : StatementLegacy.MonoidalSupercategory)
local instance : MonoidalCategory (Even (C.toSupercategory : Type)) := C.monoidalStructure.even
local instance : MonoidalCategory (StatementLegacy.Even C.toSupercategory) := C.monoidalStructure.even

/-- The underlying enriched tensor is reused with exactly its existing maps. -/
@[implicit_reducible] def fromMonoidal : MonoidalEnrichedCategory SuperVec (C.toSupercategory : Type) where
  tensor := C.monoidalStructure.tensor
  tensor_objects := C.monoidalStructure.tensor_objects
  tensor_even := C.monoidalStructure.tensor_even
  associator_isGradedNatural := by
    apply (associator_isGradedNatural_iff SuperVec _ _).mpr
    intro X X' Y Y' Z Z'
    let L := (enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects X X' Y Y' ⊗ₘ 𝟙 (SHom (C.toSupercategory : Type) Z Z')) ≫
      enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects (X ⊗ Y) (X' ⊗ Y') Z Z'
    let R := (α_ (SHom (C.toSupercategory : Type) X X') (SHom (C.toSupercategory : Type) Y Y') (SHom (C.toSupercategory : Type) Z Z')).hom ≫
      (𝟙 (SHom (C.toSupercategory : Type) X X') ⊗ₘ enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects Y Y' Z Z') ≫
        enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects X X' (Y ⊗ Z) (Y' ⊗ Z')
    suffices L ≫ eHomWhiskerLeft SuperVec ((X ⊗ Y) ⊗ Z) (α_ X' Y' Z').hom =
        R ≫ eHomWhiskerRight SuperVec (α_ X Y Z).hom (X' ⊗ (Y' ⊗ Z')) by
      simpa only [L, R, Category.assoc] using this
    apply hom_equation_of_triple
    intro f g h
    have hl : (fun a => L a (tensorPoint (tensorPoint f g) h a)) =
        StatementLegacy.tTensor C.monoidalStructure.tensor C.monoidalStructure.tensor_objects (StatementLegacy.tTensor C.monoidalStructure.tensor C.monoidalStructure.tensor_objects f g) h := by
      funext a
      change enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects _ _ _ _ a
        ((enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects X X' Y Y' ⊗ₘ 𝟙 (SHom (C.toSupercategory : Type) Z Z')) a
          (tensorPoint (tensorPoint f g) h a)) = _
      erw [congrFun (tensorPoint_map _ _ (tensorPoint f g) h) a]
      rfl
    have hr : (fun a => R a (tensorPoint (tensorPoint f g) h a)) =
        StatementLegacy.tTensor C.monoidalStructure.tensor C.monoidalStructure.tensor_objects f (StatementLegacy.tTensor C.monoidalStructure.tensor C.monoidalStructure.tensor_objects g h) := by
      funext a
      change enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects _ _ _ _ a
        ((𝟙 (SHom (C.toSupercategory : Type) X X') ⊗ₘ enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects Y Y' Z Z') a
          ((α_ (SHom (C.toSupercategory : Type) X X') (SHom (C.toSupercategory : Type) Y Y') (SHom (C.toSupercategory : Type) Z Z')).hom a
            (tensorPoint (tensorPoint f g) h a))) = _
      erw [congrFun (tensorPoint_assoc f g h) a,
        congrFun (tensorPoint_map _ _ f (tensorPoint g h)) a]
      rfl
    rw [hl, hr]
    exact C.monoidalStructure.associator_naturality f g h
  leftUnitor_isGradedNatural := by
    apply (leftUnitor_isGradedNatural_iff SuperVec _ _).mpr
    intro X Y
    let L := (λ_ (SHom (C.toSupercategory : Type) X Y)).inv ≫ (eId SuperVec (𝟙_ (Even (C.toSupercategory : Type))) ⊗ₘ 𝟙 (SHom (C.toSupercategory : Type) X Y)) ≫
      enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects (𝟙_ (Even (C.toSupercategory : Type))) (𝟙_ (Even (C.toSupercategory : Type))) X Y
    have hn := hom_equation_of_total L (𝟙 (SHom (C.toSupercategory : Type) X Y))
      (λ_ X).hom (λ_ Y).hom (fun f => by
      have hl : (fun a => L a (f a)) = StatementLegacy.tTensor C.monoidalStructure.tensor C.monoidalStructure.tensor_objects (evenPoint (eId SuperVec (𝟙_ (Even (C.toSupercategory : Type))))) f := by
        funext a
        change enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects _ _ _ _ a
          (((λ_ (SHom (C.toSupercategory : Type) X Y)).inv ≫ (eId SuperVec (𝟙_ (Even (C.toSupercategory : Type))) ⊗ₘ 𝟙 (SHom (C.toSupercategory : Type) X Y))) a (f a)) = _
        erw [congrFun (tensorPoint_even_left _ f) a]
        rfl
      rw [hl]
      exact C.monoidalStructure.left_naturality f)
    simpa only [L, Category.assoc, Category.id_comp] using hn
  rightUnitor_isGradedNatural := by
    apply (rightUnitor_isGradedNatural_iff SuperVec _ _).mpr
    intro X Y
    let L := (ρ_ (SHom (C.toSupercategory : Type) X Y)).inv ≫ (𝟙 (SHom (C.toSupercategory : Type) X Y) ⊗ₘ eId SuperVec (𝟙_ (Even (C.toSupercategory : Type)))) ≫
      enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects X Y (𝟙_ (Even (C.toSupercategory : Type))) (𝟙_ (Even (C.toSupercategory : Type)))
    have hn := hom_equation_of_total L (𝟙 (SHom (C.toSupercategory : Type) X Y))
      (ρ_ X).hom (ρ_ Y).hom (fun f => by
      have hl : (fun a => L a (f a)) = StatementLegacy.tTensor C.monoidalStructure.tensor C.monoidalStructure.tensor_objects f (evenPoint (eId SuperVec (𝟙_ (Even (C.toSupercategory : Type))))) := by
        funext a
        change enrichedTensorMap SuperVec C.monoidalStructure.tensor C.monoidalStructure.tensor_objects _ _ _ _ a
          (((ρ_ (SHom (C.toSupercategory : Type) X Y)).inv ≫ (𝟙 (SHom (C.toSupercategory : Type) X Y) ⊗ₘ eId SuperVec (𝟙_ (Even (C.toSupercategory : Type))))) a (f a)) = _
        erw [congrFun (tensorPoint_even_right f _) a]
        rfl
      rw [hl]
      exact C.monoidalStructure.right_naturality f)
    simpa only [L, Category.assoc, Category.id_comp] using hn

end RMod.EnrichedBridge
