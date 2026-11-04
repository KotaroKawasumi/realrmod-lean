import RMod.Statement.EnrichmentBridge
import RMod.Hierarchy.Instances.EvenMonoidal

/-!
# Monoidal structures in the two presentations

The enriched tensor is transported along its stated object agreement.
Its action on even morphisms is the given ordinary monoidal tensor.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.StatementLegacy.StatementBridge

/-- Normalize the enriched object's presentation to the ordinary tensor. -/
def normalizedTensor (C : MonoidalSupercategory) :
    Superfunctor (SuperTensorProduct C.super C.super) C.super :=
  changeObj C.monoidalStructure.tensor
    (fun X => tensorObj (C := Even C.super) X.1 X.2)
    (fun X => C.monoidalStructure.tensor_objects X.1 X.2)

/-- Extract the monoidal operations on the unchanged base enrichment. -/
def toMonoidalStructureData (C : MonoidalSupercategory) :
    Legacy.MonoidalSuperstructureData (toLegacySupercategory C.super).data := by
  letI : MonoidalCategory (Even C.super) := C.monoidalStructure.even
  exact {
    tensor := {
      obj X := tensorObj (C := Even C.super) X.1 X.2
      map X Y := enrichedTensorMap (C := C.super) C.monoidalStructure.tensor
        C.monoidalStructure.tensor_objects X.1 Y.1 X.2 Y.2 }
    unit := 𝟙_ (Even C.super)
    associatorHom := fun (X Y Z : Even C.super) => (α_ X Y Z).hom
    associatorInv := fun (X Y Z : Even C.super) => (α_ X Y Z).inv
    leftHom := fun (X : Even C.super) => (λ_ X).hom
    leftInv := fun (X : Even C.super) => (λ_ X).inv
    rightHom := fun (X : Even C.super) => (ρ_ X).hom
    rightInv := fun (X : Even C.super) => (ρ_ X).inv }

/-- All former structural maps are the maps of the supplied Mathlib structure. -/
def toMonoidalData (C : MonoidalSupercategory) : Legacy.MonoidalSupercategoryData where
  toSupercategoryData := (toLegacySupercategory C.super).data
  monoidal := toMonoidalStructureData C

theorem toMonoidal_eTensor (C : MonoidalSupercategory) {X X' Y Y' : Even C.super}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    Legacy.eTensor (toMonoidalData C).monoidal f g =
      ForgetEnrichment.homTo SuperVec (f ⊗ₘ g) :=
  C.monoidalStructure.tensor_even f g

theorem toMonoidal_tTensor (C : MonoidalSupercategory) {X X' Y Y' : Even C.super}
    (f : THom C.super X X') (g : THom C.super Y Y') :
    Legacy.tTensor (toMonoidalData C).monoidal f g =
      tTensor (C := C.super) C.monoidalStructure.tensor C.monoidalStructure.tensor_objects f g := rfl

/-- No coherence is assumed: all former laws follow from the supplied structure. -/
theorem toMonoidalLaws (C : MonoidalSupercategory) :
    Legacy.MonoidalSupercategoryLaws (toMonoidalData C) := by
  letI : MonoidalCategory (Even C.super) := C.monoidalStructure.even
  exact {
    toSupercategoryLaws := (toLegacySupercategory C.super).laws
    monoidal := {
      tensor := {
        map_id := (normalizedTensor C).map_id
        map_comp := (normalizedTensor C).map_comp }
      associator_hom_inv := fun (X Y Z : Even C.super) => by
        have h := CategoryTheory.Iso.hom_inv_id
          (@MonoidalCategoryStruct.associator (Even C.super) _
            (evenCategoryMonoidal C).toMonoidalCategoryStruct X Y Z)
        exact h
      associator_inv_hom := fun (X Y Z : Even C.super) => by
        have h := CategoryTheory.Iso.inv_hom_id
          (@MonoidalCategoryStruct.associator (Even C.super) _
            (evenCategoryMonoidal C).toMonoidalCategoryStruct X Y Z)
        exact h
      left_hom_inv := fun (X : Even C.super) => by
        have h := CategoryTheory.Iso.hom_inv_id
          (@MonoidalCategoryStruct.leftUnitor (Even C.super) _
            (evenCategoryMonoidal C).toMonoidalCategoryStruct X)
        exact h
      left_inv_hom := fun (X : Even C.super) => by
        have h := CategoryTheory.Iso.inv_hom_id
          (@MonoidalCategoryStruct.leftUnitor (Even C.super) _
            (evenCategoryMonoidal C).toMonoidalCategoryStruct X)
        exact h
      right_hom_inv := fun (X : Even C.super) => by
        have h := CategoryTheory.Iso.hom_inv_id
          (@MonoidalCategoryStruct.rightUnitor (Even C.super) _
            (evenCategoryMonoidal C).toMonoidalCategoryStruct X)
        exact h
      right_inv_hom := fun (X : Even C.super) => by
        have h := CategoryTheory.Iso.inv_hom_id
          (@MonoidalCategoryStruct.rightUnitor (Even C.super) _
            (evenCategoryMonoidal C).toMonoidalCategoryStruct X)
        exact h
      associator_naturality := C.monoidalStructure.associator_naturality
      left_naturality := C.monoidalStructure.left_naturality
      right_naturality := C.monoidalStructure.right_naturality
      pentagon := fun (W X Y Z : Even C.super) => by
        change Legacy.eComp _ (Legacy.eComp _
          (Legacy.eTensor (toMonoidalData C).monoidal (α_ W X Y).hom (𝟙 Z))
          (α_ W (X ⊗ Y) Z).hom)
          (Legacy.eTensor (toMonoidalData C).monoidal (𝟙 W) (α_ X Y Z).hom) = _
        rw [toMonoidal_eTensor, toMonoidal_eTensor]
        change (((α_ W X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom) ≫
          (𝟙 W ⊗ₘ (α_ X Y Z).hom) =
            (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom
        simpa only [tensorHom_id, id_tensorHom, Category.assoc] using
          (MonoidalCategory.pentagon W X Y Z)
      triangle := fun (X Y : Even C.super) => by
        change Legacy.eComp (toMonoidalData C).toSupercategoryData (α_ X (𝟙_ (Even C.super)) Y).hom
          (Legacy.eTensor (toMonoidalData C).monoidal (𝟙 X) (λ_ Y).hom) =
          Legacy.eTensor (toMonoidalData C).monoidal (ρ_ X).hom (𝟙 Y)
        rw [toMonoidal_eTensor, toMonoidal_eTensor]
        change (α_ X (𝟙_ (Even C.super)) Y).hom ≫ (𝟙 X ⊗ₘ (λ_ Y).hom) =
          (ρ_ X).hom ⊗ₘ 𝟙 Y
        simpa only [tensorHom_id, id_tensorHom] using (MonoidalCategory.triangle X Y) }
  }

def toMonoidal (C : MonoidalSupercategory) : Legacy.MonoidalSupercategory :=
  ⟨toMonoidalData C, toMonoidalLaws C⟩

/-- Rebundle the already proved former structure with Mathlib's monoidal category. -/
def fromMonoidal (C : Legacy.MonoidalSupercategory) : MonoidalSupercategory where
  toSupercategory := fromSuper C.super
  monoidalStructure := {
    even := Legacy.evenCategoryMonoidal C
    tensor := {
      obj := C.data.monoidal.tensor.obj
      map := C.data.monoidal.tensor.map
      map_id := C.laws.monoidal.tensor.map_id
      map_comp := C.laws.monoidal.tensor.map_comp }
    tensor_objects := fun _ _ => rfl
    tensor_even := by
      intro X X' Y Y' f g
      simp only [enrichedTensorMap, eqToHom_refl, Category.comp_id]
      rfl
    associator_naturality := by
      intro X X' Y Y' Z Z' f g h
      exact C.laws.monoidal.associator_naturality f g h
    left_naturality := by
      intro X Y f
      exact C.laws.monoidal.left_naturality f
    right_naturality := by
      intro X Y f
      exact C.laws.monoidal.right_naturality f }

/-- Monoidal coherence proofs do not affect equality of structures. -/
theorem monoidal_eq_of_data_eq {A : Type} [Category A] {M N : MonoidalCategory A}
    (h : M.toMonoidalCategoryStruct = N.toMonoidalCategoryStruct) : M = N := by
  cases M
  cases N
  cases h
  rfl

/-- Reconstructing the even category retains every supplied monoidal operation. -/
theorem toMonoidal_even (C : MonoidalSupercategory) :
    Legacy.evenCategoryMonoidal (toMonoidal C) = evenCategoryMonoidal C := by
  apply monoidal_eq_of_data_eq
  have ht : @Legacy.eTensor _ (toMonoidalData C).monoidal =
      @MonoidalCategory.tensorHom (Even C.super) _ _ := by
    funext X X' Y Y' f g
    exact toMonoidal_eTensor C f g
  have hl : (fun (X : Even C.super) {Y Z : Even C.super} (f : Y ⟶ Z) =>
      Legacy.eTensor (toMonoidalData C).monoidal (eId SuperVec X) f) =
      @MonoidalCategory.whiskerLeft (Even C.super) _ _ := by
    funext X Y Z f
    rw [toMonoidal_eTensor]
    exact id_tensorHom X f
  have hr : (fun {X Y : Even C.super} (f : X ⟶ Y) (Z : Even C.super) =>
      Legacy.eTensor (toMonoidalData C).monoidal f (eId SuperVec Z)) =
      @MonoidalCategory.whiskerRight (Even C.super) _ _ := by
    funext X Y f Z
    rw [toMonoidal_eTensor]
    exact tensorHom_id f Z
  change ({
    tensorObj := tensorObj (C := Even C.super)
    whiskerLeft := fun X {_ _} f => Legacy.eTensor (toMonoidalData C).monoidal (eId SuperVec X) f
    whiskerRight := fun {_ _} f Z => Legacy.eTensor (toMonoidalData C).monoidal f (eId SuperVec Z)
    tensorHom := @Legacy.eTensor _ (toMonoidalData C).monoidal
    tensorUnit := 𝟙_ (Even C.super)
    associator := fun X Y Z => α_ X Y Z
    leftUnitor := fun X => λ_ X
    rightUnitor := fun X => ρ_ X } : MonoidalCategoryStruct (Even C.super)) = _
  rw [hl, hr, ht]
  rfl

end RMod.StatementLegacy.StatementBridge
