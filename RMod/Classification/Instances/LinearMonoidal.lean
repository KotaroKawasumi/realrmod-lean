import RMod.Classification.Instances.EndGrading
import Superfusion.Category.Even

/-!
# Reusing the monoidal and even-category interfaces

The raw tensor and coherence maps give the existing monoidal supercategory
interface. Restriction to even morphisms then provides Mathlib's ordinary
monoidal category, including its preadditive and linear instances. No new
tensor operation or sign-free interchange law is imposed on odd maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.LinearCategory

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{u, v})

instance monoidalStruct : MonoidalCategoryStruct (LinearCategory C) where
  tensorObj := C.data.tensorObj
  tensorHom := C.data.tensorHom
  whiskerLeft := C.data.whiskerLeft
  whiskerRight := C.data.whiskerRight
  tensorUnit := C.data.tensorUnit
  associator X Y Z :=
    { hom := C.data.associatorHom X Y Z
      inv := C.data.associatorInv X Y Z
      hom_inv_id := C.laws.associator_hom_inv X Y Z
      inv_hom_id := C.laws.associator_inv_hom X Y Z }
  leftUnitor X :=
    { hom := C.data.leftUnitorHom X
      inv := C.data.leftUnitorInv X
      hom_inv_id := C.laws.left_unitor_hom_inv X
      inv_hom_id := C.laws.left_unitor_inv_hom X }
  rightUnitor X :=
    { hom := C.data.rightUnitorHom X
      inv := C.data.rightUnitorInv X
      hom_inv_id := C.laws.right_unitor_hom_inv X
      inv_hom_id := C.laws.right_unitor_inv_hom X }

instance monoidalSupercategory :
    Superfusion.Category.MonoidalSupercategory ℝ (LinearCategory C) where
  tensorHom_mem := C.laws.tensor_grade
  tensor_id := C.laws.tensor_id
  tensor_add_left := C.laws.tensor_add_left
  tensor_add_right := C.laws.tensor_add_right
  tensor_smul_left := C.laws.tensor_smul_left
  tensor_smul_right := C.laws.tensor_smul_right
  super_interchange := C.laws.super_interchange
  whiskerLeft_eq := fun _ {_ _} _ => rfl
  whiskerRight_eq := fun {_ _} _ _ => rfl
  associator_hom_mem := C.laws.associator_hom_even
  associator_inv_mem := C.laws.associator_inv_even
  associator_naturality := C.laws.associator_naturality
  leftUnitor_hom_mem := C.laws.left_unitor_hom_even
  leftUnitor_inv_mem := C.laws.left_unitor_inv_even
  leftUnitor_naturality := C.laws.left_unitor_naturality
  rightUnitor_hom_mem := C.laws.right_unitor_hom_even
  rightUnitor_inv_mem := C.laws.right_unitor_inv_even
  rightUnitor_naturality := C.laws.right_unitor_naturality
  pentagon W X Y Z := by
    exact (C.laws.comp_assoc _ _ _).symm.trans (C.laws.pentagon W X Y Z)
  triangle := C.laws.triangle

end RMod.Classification.LinearCategory
