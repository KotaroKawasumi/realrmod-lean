import RMod.BrundanEllis.StackingProductTensor
import RMod.BrundanEllis.StackingProductEven

/-! The ordinary monoidal data of the super product. Tensor maps come from
the genuine enriched tensor functor; associators and unitors are the images
of the two given even structural isomorphisms. Laws are proved separately. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable (A B : Type) [SuperCategory A] [SuperCategory B]

/-- Embed a pair of even maps as their pure even tensor. -/
def productPair : Even A × Even B ⥤ Even (SuperTensorProduct A B) :=
  evenPairFunctor (EnrichedFunctor.id SuperVec (SuperTensorProduct A B))

variable [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]

/-- Display the tensor functor with its componentwise object formula. -/
def productTensorFunctor :
    Even (SuperTensorProduct A B) × Even (SuperTensorProduct A B) ⥤
      Even (SuperTensorProduct A B) where
  obj X := evenObj _ ((X.1.1 ⊗ X.2.1 : Even A), (X.1.2 ⊗ X.2.2 : Even B))
  map f := (evenPairFunctor (productTensor A B)).map f
  map_id X := (evenPairFunctor (productTensor A B)).map_id X
  map_comp f g := (evenPairFunctor (productTensor A B)).map_comp f g

instance productMonoidalStruct : MonoidalCategoryStruct (Even (SuperTensorProduct A B)) where
  tensorObj X Y := evenObj _ ((X.1 ⊗ Y.1 : Even A), (X.2 ⊗ Y.2 : Even B))
  whiskerLeft X Y Z g := (productTensorFunctor A B).map (X := (X, Y)) (Y := (X, Z)) (𝟙 X, g)
  whiskerRight {X X'} f Y := (productTensorFunctor A B).map (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y)
  tensorHom {X X' Y Y'} f g := (productTensorFunctor A B).map (X := (X, Y)) (Y := (X', Y')) (f, g)
  tensorUnit := evenObj _ (𝟙_ (Even A), 𝟙_ (Even B))
  associator X Y Z := (productPair A B).mapIso
    ((MonoidalCategory.associator (C := Even A) X.1 Y.1 Z.1).prod (MonoidalCategory.associator (C := Even B) X.2 Y.2 Z.2))
  leftUnitor X := (productPair A B).mapIso ((MonoidalCategory.leftUnitor (C := Even A) X.1).prod (MonoidalCategory.leftUnitor (C := Even B) X.2))
  rightUnitor X := (productPair A B).mapIso ((MonoidalCategory.rightUnitor (C := Even A) X.1).prod (MonoidalCategory.rightUnitor (C := Even B) X.2))

end RMod.BrundanEllis.Stacking
