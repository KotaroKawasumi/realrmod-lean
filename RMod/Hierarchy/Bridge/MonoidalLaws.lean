import RMod.Hierarchy.Bridge.TensorLaws
import RMod.Hierarchy.Bridge.MonoidalNaturality
import RMod.Hierarchy.Instances.EvenMonoidal

/-!
# The old monoidal structure in the enriched hierarchy

The even equivalence identifies all specified coherence maps and tensor
products. Its faithfulness transfers the pentagon, triangle, and inverse
identities; total naturality was checked on both parity components.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

@[simp]
theorem evenHomEquiv_associatorHom (X Y Z : C.data.Obj) :
    evenHomEquiv C _ _ ((ofOldMonoidalStructureData C).associatorHom X Y Z) =
      (α_ (oldEvenObj C X) (oldEvenObj C Y) (oldEvenObj C Z)).hom := by
  apply WideSubcategory.hom_ext
  rw [evenHomEquiv_apply]
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]
  rfl

@[simp]
theorem evenHomEquiv_associatorInv (X Y Z : C.data.Obj) :
    evenHomEquiv C _ _ ((ofOldMonoidalStructureData C).associatorInv X Y Z) =
      (α_ (oldEvenObj C X) (oldEvenObj C Y) (oldEvenObj C Z)).inv := by
  apply WideSubcategory.hom_ext
  rw [evenHomEquiv_apply]
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]
  rfl

@[simp]
theorem evenHomEquiv_leftHom (X : C.data.Obj) :
    evenHomEquiv C _ _ ((ofOldMonoidalStructureData C).leftHom X) =
      (λ_ (oldEvenObj C X)).hom := by
  apply WideSubcategory.hom_ext
  rw [evenHomEquiv_apply]
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]
  rfl

@[simp]
theorem evenHomEquiv_leftInv (X : C.data.Obj) :
    evenHomEquiv C _ _ ((ofOldMonoidalStructureData C).leftInv X) =
      (λ_ (oldEvenObj C X)).inv := by
  apply WideSubcategory.hom_ext
  rw [evenHomEquiv_apply]
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]
  rfl

@[simp]
theorem evenHomEquiv_rightHom (X : C.data.Obj) :
    evenHomEquiv C _ _ ((ofOldMonoidalStructureData C).rightHom X) =
      (ρ_ (oldEvenObj C X)).hom := by
  apply WideSubcategory.hom_ext
  rw [evenHomEquiv_apply]
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]
  rfl

@[simp]
theorem evenHomEquiv_rightInv (X : C.data.Obj) :
    evenHomEquiv C _ _ ((ofOldMonoidalStructureData C).rightInv X) =
      (ρ_ (oldEvenObj C X)).inv := by
  apply WideSubcategory.hom_ext
  rw [evenHomEquiv_apply]
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]
  rfl

theorem oldEven_comp_value (X Y Z : C.data.Obj)
    (f : EHom (ofOldSupercategoryData C) X Y) (g : EHom (ofOldSupercategoryData C) Y Z) :
    (evenPoint (eComp (ofOldSupercategoryData C) f g) 0).val =
      C.data.comp (evenPoint f 0).val (evenPoint g 0).val :=
  congrArg (fun f : oldEvenObj C X ⟶ oldEvenObj C Z => f.hom) (evenHomEquiv_comp C X Y Z f g)

theorem oldEven_tensor_value {X X' Y Y' : C.data.Obj}
    (f : EHom (ofOldSupercategoryData C) X X') (g : EHom (ofOldSupercategoryData C) Y Y') :
    (evenPoint (eTensor (ofOldMonoidalStructureData C) f g) 0).val =
      C.data.tensorHom (evenPoint f 0).val (evenPoint g 0).val :=
  congrArg (fun f : oldEvenObj C (C.data.tensorObj X Y) ⟶
    oldEvenObj C (C.data.tensorObj X' Y') => f.hom) (evenHomEquiv_tensor C f g)

theorem oldEven_id_value (X : C.data.Obj) :
    (evenPoint ((ofOldSupercategoryData C).id X) 0).val = C.data.id X := oldEnrichedId_zero C X

theorem oldEven_associatorHom_value (X Y Z : C.data.Obj) :
    (evenPoint ((ofOldMonoidalStructureData C).associatorHom X Y Z) 0).val =
      C.data.associatorHom X Y Z := by
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]

theorem oldEven_associatorInv_value (X Y Z : C.data.Obj) :
    (evenPoint ((ofOldMonoidalStructureData C).associatorInv X Y Z) 0).val =
      C.data.associatorInv X Y Z := by
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]

theorem oldEven_leftHom_value (X : C.data.Obj) :
    (evenPoint ((ofOldMonoidalStructureData C).leftHom X) 0).val =
      C.data.leftUnitorHom X := by
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]

theorem oldEven_leftInv_value (X : C.data.Obj) :
    (evenPoint ((ofOldMonoidalStructureData C).leftInv X) 0).val =
      C.data.leftUnitorInv X := by
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]

theorem oldEven_rightHom_value (X : C.data.Obj) :
    (evenPoint ((ofOldMonoidalStructureData C).rightHom X) 0).val =
      C.data.rightUnitorHom X := by
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]

theorem oldEven_rightInv_value (X : C.data.Obj) :
    (evenPoint ((ofOldMonoidalStructureData C).rightInv X) 0).val =
      C.data.rightUnitorInv X := by
  dsimp only [ofOldMonoidalStructureData, evenPoint]
  rw [homogeneousPoint_map_same]

theorem ofOldPentagon (W X Y Z : C.data.Obj) :
    eComp (ofOldSupercategoryData C)
      (eComp (ofOldSupercategoryData C)
        (eTensor (ofOldMonoidalStructureData C)
          ((ofOldMonoidalStructureData C).associatorHom W X Y) ((ofOldSupercategoryData C).id Z))
        ((ofOldMonoidalStructureData C).associatorHom W (C.data.tensorObj X Y) Z))
      (eTensor (ofOldMonoidalStructureData C) ((ofOldSupercategoryData C).id W)
        ((ofOldMonoidalStructureData C).associatorHom X Y Z)) =
    eComp (ofOldSupercategoryData C)
      ((ofOldMonoidalStructureData C).associatorHom (C.data.tensorObj W X) Y Z)
      ((ofOldMonoidalStructureData C).associatorHom W X (C.data.tensorObj Y Z)) := by
  apply (homogeneousHomEquiv _ 0).injective
  apply Subtype.ext
  dsimp only [homogeneousHomEquiv]
  erw [oldEven_comp_value C (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj W X) Y) Z) (C.data.tensorObj W (C.data.tensorObj (C.data.tensorObj X Y) Z)) (C.data.tensorObj W (C.data.tensorObj X (C.data.tensorObj Y Z))) (eComp (ofOldSupercategoryData C) (eTensor (ofOldMonoidalStructureData C) ((ofOldMonoidalStructureData C).associatorHom W X Y) ((ofOldSupercategoryData C).id Z)) ((ofOldMonoidalStructureData C).associatorHom W (C.data.tensorObj X Y) Z)) (eTensor (ofOldMonoidalStructureData C) ((ofOldSupercategoryData C).id W) ((ofOldMonoidalStructureData C).associatorHom X Y Z)),
    oldEven_comp_value C (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj W X) Y) Z) (C.data.tensorObj (C.data.tensorObj W (C.data.tensorObj X Y)) Z) (C.data.tensorObj W (C.data.tensorObj (C.data.tensorObj X Y) Z)) (eTensor (ofOldMonoidalStructureData C) ((ofOldMonoidalStructureData C).associatorHom W X Y) ((ofOldSupercategoryData C).id Z)) ((ofOldMonoidalStructureData C).associatorHom W (C.data.tensorObj X Y) Z),
    oldEven_comp_value C (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj W X) Y) Z) (C.data.tensorObj (C.data.tensorObj W X) (C.data.tensorObj Y Z)) (C.data.tensorObj W (C.data.tensorObj X (C.data.tensorObj Y Z))) ((ofOldMonoidalStructureData C).associatorHom (C.data.tensorObj W X) Y Z) ((ofOldMonoidalStructureData C).associatorHom W X (C.data.tensorObj Y Z)),
    oldEven_tensor_value C ((ofOldMonoidalStructureData C).associatorHom W X Y) ((ofOldSupercategoryData C).id Z),
    oldEven_tensor_value C ((ofOldSupercategoryData C).id W) ((ofOldMonoidalStructureData C).associatorHom X Y Z),
    oldEven_associatorHom_value C W X Y,
    oldEven_associatorHom_value C W (C.data.tensorObj X Y) Z,
    oldEven_associatorHom_value C X Y Z,
    oldEven_associatorHom_value C (C.data.tensorObj W X) Y Z,
    oldEven_associatorHom_value C W X (C.data.tensorObj Y Z),
    oldEven_id_value C W,
    oldEven_id_value C Z]
  exact C.laws.pentagon W X Y Z

theorem ofOldTriangle (X Y : C.data.Obj) :
    eComp (ofOldSupercategoryData C)
      ((ofOldMonoidalStructureData C).associatorHom X C.data.tensorUnit Y)
      (eTensor (ofOldMonoidalStructureData C) ((ofOldSupercategoryData C).id X)
        ((ofOldMonoidalStructureData C).leftHom Y)) =
    eTensor (ofOldMonoidalStructureData C) ((ofOldMonoidalStructureData C).rightHom X)
      ((ofOldSupercategoryData C).id Y) := by
  apply (homogeneousHomEquiv _ 0).injective
  apply Subtype.ext
  dsimp only [homogeneousHomEquiv]
  erw [oldEven_comp_value C (C.data.tensorObj (C.data.tensorObj X C.data.tensorUnit) Y) (C.data.tensorObj X (C.data.tensorObj C.data.tensorUnit Y)) (C.data.tensorObj X Y) ((ofOldMonoidalStructureData C).associatorHom X C.data.tensorUnit Y) (eTensor (ofOldMonoidalStructureData C) ((ofOldSupercategoryData C).id X) ((ofOldMonoidalStructureData C).leftHom Y)),
    oldEven_tensor_value C ((ofOldSupercategoryData C).id X) ((ofOldMonoidalStructureData C).leftHom Y),
    oldEven_tensor_value C ((ofOldMonoidalStructureData C).rightHom X) ((ofOldSupercategoryData C).id Y),
    oldEven_associatorHom_value C X C.data.tensorUnit Y,
    oldEven_leftHom_value C Y,
    oldEven_rightHom_value C X,
    oldEven_id_value C X,
    oldEven_id_value C Y]
  exact C.laws.triangle X Y

theorem ofOldMonoidalStructureLaws :
    MonoidalSuperstructureLaws (ofOldSupercategory C) (ofOldMonoidalStructureData C) where
  tensor := ofOldTensorLaws C
  associator_hom_inv X Y Z := by
    apply (evenHomEquiv C _ _).injective
    erw [evenHomEquiv_comp C, evenHomEquiv_associatorHom C, evenHomEquiv_associatorInv C, evenHomEquiv_id C]
    exact Iso.hom_inv_id _
  associator_inv_hom X Y Z := by
    apply (evenHomEquiv C _ _).injective
    erw [evenHomEquiv_comp C, evenHomEquiv_associatorHom C, evenHomEquiv_associatorInv C, evenHomEquiv_id C]
    exact Iso.inv_hom_id _
  left_hom_inv X := by
    apply (evenHomEquiv C _ _).injective
    erw [evenHomEquiv_comp C, evenHomEquiv_leftHom C, evenHomEquiv_leftInv C, evenHomEquiv_id C]
    exact Iso.hom_inv_id _
  left_inv_hom X := by
    apply (evenHomEquiv C _ _).injective
    erw [evenHomEquiv_comp C, evenHomEquiv_leftHom C, evenHomEquiv_leftInv C, evenHomEquiv_id C]
    exact Iso.inv_hom_id _
  right_hom_inv X := by
    apply (evenHomEquiv C _ _).injective
    erw [evenHomEquiv_comp C, evenHomEquiv_rightHom C, evenHomEquiv_rightInv C, evenHomEquiv_id C]
    exact Iso.hom_inv_id _
  right_inv_hom X := by
    apply (evenHomEquiv C _ _).injective
    erw [evenHomEquiv_comp C, evenHomEquiv_rightHom C, evenHomEquiv_rightInv C, evenHomEquiv_id C]
    exact Iso.inv_hom_id _
  associator_naturality := ofOld_associator_naturality C
  left_naturality := ofOld_left_naturality C
  right_naturality := ofOld_right_naturality C
  pentagon := ofOldPentagon C
  triangle := ofOldTriangle C

def ofOldMonoidalSupercategory : MonoidalSupercategory :=
  ⟨⟨ofOldSupercategoryData C, ofOldMonoidalStructureData C⟩,
    ⟨ofOldSupercategoryLaws C, ofOldMonoidalStructureLaws C⟩⟩

end RMod.Legacy.Hierarchy
