import RMod.Hierarchy.Instances.EvenMonoidal

/-!
# Additivity of the even tensor product

The even tensor operation is obtained from the linear map on enriched Hom
objects, so its whiskering operations preserve zeros and addition.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy

instance evenMonoidalPreadditive (C : MonoidalSupercategory) :
    MonoidalPreadditive (Even C.super) where
  whiskerLeft_zero {X Y Z} := by
    change eTensor C.data.monoidal (C.data.id X) (0 : EHom C.super.data Y Z) = 0
    simp [eTensor]
  zero_whiskerRight {X Y Z} := by
    change eTensor C.data.monoidal (0 : EHom C.super.data Y Z) (C.data.id X) = 0
    simp [eTensor]
  whiskerLeft_add {X Y Z} f g := by
    change eTensor C.data.monoidal (C.data.id X) (f + g) =
      eTensor C.data.monoidal (C.data.id X) f + eTensor C.data.monoidal (C.data.id X) g
    simp [eTensor, MonoidalPreadditive.tensor_add, Preadditive.comp_add, Preadditive.add_comp]
  add_whiskerRight {X Y Z} f g := by
    change eTensor C.data.monoidal (f + g) (C.data.id X) =
      eTensor C.data.monoidal f (C.data.id X) + eTensor C.data.monoidal g (C.data.id X)
    simp [eTensor, MonoidalPreadditive.add_tensor, Preadditive.comp_add, Preadditive.add_comp]

end RMod.Legacy
