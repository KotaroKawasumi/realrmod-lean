import RMod.BrundanEllis.Surface
import RMod.BrundanEllis.StackingEnrichedShuffle
import RMod.Enriched.Compatibility

/-! The tensor on the uncompleted super product reorders the middle two
factors and applies the given tensor functors. Its Hom map is exactly the
Koszul interchange followed by the two component tensor maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable (A B : Type) [SuperCategory A] [SuperCategory B]
  [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]

def productTensor :
    SuperFunctor (SuperTensorProduct (SuperTensorProduct A B) (SuperTensorProduct A B))
      (SuperTensorProduct A B) :=
  (enrichedShuffle SuperVec A B A B).comp SuperVec
    (RMod.tensorEnrichedFunctors SuperVec
      (RMod.alignedTensor SuperVec (MonoidalSuperCategory.tensor (C := A))
        MonoidalSuperCategory.tensor_objects)
      (RMod.alignedTensor SuperVec (MonoidalSuperCategory.tensor (C := B))
        MonoidalSuperCategory.tensor_objects))

theorem productTensor_obj (X Y : SuperTensorProduct A B) :
    (productTensor A B).obj (X, Y) =
      ((X.1 ⊗ Y.1 : Even A), (X.2 ⊗ Y.2 : Even B)) := rfl

theorem productTensor_map
    (X Y : SuperTensorProduct (SuperTensorProduct A B) (SuperTensorProduct A B)) :
    (productTensor A B).map X Y =
      tensorμ (SHom A X.1.1 Y.1.1) (SHom B X.1.2 Y.1.2)
        (SHom A X.2.1 Y.2.1) (SHom B X.2.2 Y.2.2) ≫
      (enrichedTensorMap (C := A) (MonoidalSuperCategory.tensor (C := A))
        MonoidalSuperCategory.tensor_objects X.1.1 Y.1.1 X.2.1 Y.2.1 ⊗ₘ
       enrichedTensorMap (C := B) (MonoidalSuperCategory.tensor (C := B))
        MonoidalSuperCategory.tensor_objects X.1.2 Y.1.2 X.2.2 Y.2.2) := by
  change (enrichedShuffle SuperVec A B A B).map X Y ≫ _ = _
  rw [enrichedShuffle_map]
  congr 1

end RMod.BrundanEllis.Stacking
