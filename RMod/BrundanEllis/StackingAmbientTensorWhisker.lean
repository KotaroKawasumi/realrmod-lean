import RMod.BrundanEllis.StackingAlignedTensor
import RMod.BrundanEllis.StackingFunctorWhisker
import RMod.BrundanEllis.StackingProductWhisker
import RMod.BrundanEllis.StackingKaroubiNaturality

/-! Tensoring full Hom spaces commutes with even precomposition and postcomposition. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalSuperCategory C]
/-- Tensoring full Hom objects commutes with postcomposition by even arrows. -/
@[reassoc] theorem ambientTensor_post (X Y : Even C)
    {X' X'' Y' Y'' : Even C} (f : X' ⟶ X'') (g : Y' ⟶ Y'') :
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      eHomWhiskerLeft SuperVec (X ⊗ Y) (f ⊗ₘ g) =
    (eHomWhiskerLeft SuperVec X f ⊗ₘ eHomWhiskerLeft SuperVec Y g) ≫
      KaroubiSuper.ambientTensor X X'' Y Y'' := by
  have h := superFunctor_post (alignedSuperTensor C)
    ((productPair C C).obj (X, Y)) ((productPair C C).map (X := (X', Y')) (Y := (X'', Y'')) (f, g))
  rw [product_whisker_left] at h
  change (alignedSuperTensor C).map (X, Y) (X', Y') ≫
    eHomWhiskerLeft SuperVec (X ⊗ Y)
      ((evenPairFunctor (alignedSuperTensor C)).map (X := (X', Y')) (Y := (X'', Y'')) (f, g)) =
    (eHomWhiskerLeft SuperVec X f ⊗ₘ eHomWhiskerLeft SuperVec Y g) ≫
      (alignedSuperTensor C).map (X, Y) (X'', Y'') at h
  rw [alignedSuperTensor_map C (X, Y) (X', Y'),
    alignedSuperTensor_map C (X, Y) (X'', Y''), alignedSuperTensor_even] at h
  exact h

/-- Tensoring full Hom objects commutes with precomposition by even arrows. -/
@[reassoc] theorem ambientTensor_pre {X X' Y Y' : Even C}
    (f : X ⟶ X') (g : Y ⟶ Y') (Z W : Even C) :
    KaroubiSuper.ambientTensor X' Z Y' W ≫
      eHomWhiskerRight SuperVec (f ⊗ₘ g) (Z ⊗ W) =
    (eHomWhiskerRight SuperVec f Z ⊗ₘ eHomWhiskerRight SuperVec g W) ≫
      KaroubiSuper.ambientTensor X Z Y W := by
  have h := superFunctor_pre (alignedSuperTensor C)
    ((productPair C C).map (X := (X, Y)) (Y := (X', Y')) (f, g)) ((productPair C C).obj (Z, W))
  rw [product_whisker_right] at h
  change (alignedSuperTensor C).map (X', Y') (Z, W) ≫
    eHomWhiskerRight SuperVec
      ((evenPairFunctor (alignedSuperTensor C)).map (X := (X, Y)) (Y := (X', Y')) (f, g)) (Z ⊗ W) =
    (eHomWhiskerRight SuperVec f Z ⊗ₘ eHomWhiskerRight SuperVec g W) ≫
      (alignedSuperTensor C).map (X, Y) (Z, W) at h
  rw [alignedSuperTensor_map C (X', Y') (Z, W),
    alignedSuperTensor_map C (X, Y) (Z, W), alignedSuperTensor_even] at h
  exact h


end RMod.BrundanEllis.Stacking
