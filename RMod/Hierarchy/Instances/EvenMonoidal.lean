import RMod.Hierarchy.Instances.EvenTensor
import RMod.Hierarchy.Instances.TensorPoints
import RMod.Hierarchy.Instances.EvenLinear

/-!
# The even monoidal category

The tensor, unit, and comparison maps are precisely the specified super data.
Naturality on total morphisms restricts to degree zero by injectivity of the
basis-point representation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy

instance evenCategoryMonoidal (C : MonoidalSupercategory) : MonoidalCategory (Even C.super) where
  tensorObj X Y := C.data.monoidal.tensor.obj (X, Y)
  tensorHom := eTensor C.data.monoidal
  whiskerLeft X {_ _} f := eTensor C.data.monoidal (C.data.id X) f
  whiskerRight {_ _} f Y := eTensor C.data.monoidal f (C.data.id Y)
  tensorUnit := C.data.monoidal.unit
  associator X Y Z :=
    ⟨C.data.monoidal.associatorHom X Y Z, C.data.monoidal.associatorInv X Y Z,
      C.laws.monoidal.associator_hom_inv X Y Z, C.laws.monoidal.associator_inv_hom X Y Z⟩
  leftUnitor X := ⟨C.data.monoidal.leftHom X, C.data.monoidal.leftInv X,
    C.laws.monoidal.left_hom_inv X, C.laws.monoidal.left_inv_hom X⟩
  rightUnitor X := ⟨C.data.monoidal.rightHom X, C.data.monoidal.rightInv X,
    C.laws.monoidal.right_hom_inv X, C.laws.monoidal.right_inv_hom X⟩
  tensorHom_def := by
    intro X Y X' Y' f g
    change eTensor C.data.monoidal f g = eComp C.super.data
      (eTensor C.data.monoidal f (C.data.id X'))
      (eTensor C.data.monoidal (C.data.id Y) g)
    erw [eTensor_comp (C := C.super) C.data.monoidal C.laws.monoidal]
    erw [eComp_id C.super, id_eComp C.super]
  id_tensorHom_id := by
    intro X Y
    exact eTensor_id (C := C.super) C.data.monoidal C.laws.monoidal X Y
  tensorHom_comp_tensorHom := by
    intro X Y Z X' Y' Z' f g q r
    exact eTensor_comp C.data.monoidal C.laws.monoidal f g q r
  whiskerLeft_id := by
    intro X Y
    exact eTensor_id (C := C.super) C.data.monoidal C.laws.monoidal X Y
  id_whiskerRight := by
    intro X Y
    exact eTensor_id (C := C.super) C.data.monoidal C.laws.monoidal X Y
  associator_naturality := by
    intro X Y Z X' Y' Z' f g h
    change eComp C.super.data
      (eTensor C.data.monoidal (eTensor C.data.monoidal f g) h)
      (C.data.monoidal.associatorHom X' Y' Z') =
      eComp C.super.data (C.data.monoidal.associatorHom X Y Z)
        (eTensor C.data.monoidal f (eTensor C.data.monoidal g h))
    apply evenPoint_injective
    simp only [evenPoint_comp, evenPoint_tensor]
    exact C.laws.monoidal.associator_naturality (evenPoint f) (evenPoint g) (evenPoint h)
  leftUnitor_naturality := by
    intro X Y f
    change eComp C.super.data (eTensor C.data.monoidal (C.data.id C.data.monoidal.unit) f)
      (C.data.monoidal.leftHom Y) = eComp C.super.data (C.data.monoidal.leftHom X) f
    apply evenPoint_injective
    simp only [evenPoint_comp, evenPoint_tensor]
    exact C.laws.monoidal.left_naturality (evenPoint f)
  rightUnitor_naturality := by
    intro X Y f
    change eComp C.super.data (eTensor C.data.monoidal f (C.data.id C.data.monoidal.unit))
      (C.data.monoidal.rightHom Y) = eComp C.super.data (C.data.monoidal.rightHom X) f
    apply evenPoint_injective
    simp only [evenPoint_comp, evenPoint_tensor]
    exact C.laws.monoidal.right_naturality (evenPoint f)
  pentagon := by
    intro W X Y Z
    rw [← Category.assoc]
    exact C.laws.monoidal.pentagon W X Y Z
  triangle := C.laws.monoidal.triangle

end RMod.Legacy
