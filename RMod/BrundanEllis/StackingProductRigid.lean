import RMod.BrundanEllis.StackingProductSuperMonoidal
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! The raw super tensor product has componentwise dual objects. Pairing
maps are pure even tensors of the component pairings, and their snakes
are the images of the two component snake equations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {A B : Type} [SuperCategory A] [SuperCategory B]
  [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]

theorem productPair_whiskerLeft (X : Even A × Even B) {Y Z : Even A × Even B} (f : Y ⟶ Z) :
    (productPair A B).obj X ◁ (productPair A B).map f = (productPair A B).map (X ◁ f) := by
  have h := productPair_tensor (𝟙 X) f
  rw [CategoryTheory.Functor.map_id] at h
  simpa only [id_tensorHom] using h

theorem productPair_whiskerRight {X Y : Even A × Even B} (f : X ⟶ Y) (Z : Even A × Even B) :
    (productPair A B).map f ▷ (productPair A B).obj Z = (productPair A B).map (f ▷ Z) := by
  have h := productPair_tensor f (𝟙 Z)
  rw [CategoryTheory.Functor.map_id] at h
  simpa only [tensorHom_id] using h

theorem productPair_associator_hom (X Y Z : Even A × Even B) :
    (α_ ((productPair A B).obj X) ((productPair A B).obj Y) ((productPair A B).obj Z)).hom =
      (productPair A B).map (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z)) (α_ X Y Z).hom := rfl

theorem productPair_leftUnitor_hom (X : Even A × Even B) :
    (λ_ ((productPair A B).obj X)).hom =
      (productPair A B).map (X := (𝟙_ (Even A × Even B)) ⊗ X) (Y := X) (λ_ X).hom := rfl

theorem productPair_rightUnitor_hom (X : Even A × Even B) :
    (ρ_ ((productPair A B).obj X)).hom =
      (productPair A B).map (X := X ⊗ (𝟙_ (Even A × Even B))) (Y := X) (ρ_ X).hom := rfl

theorem productPair_associator_inv (X Y Z : Even A × Even B) :
    (α_ ((productPair A B).obj X) ((productPair A B).obj Y) ((productPair A B).obj Z)).inv =
      (productPair A B).map (X := X ⊗ (Y ⊗ Z)) (Y := (X ⊗ Y) ⊗ Z) (α_ X Y Z).inv := rfl

theorem productPair_leftUnitor_inv (X : Even A × Even B) :
    (λ_ ((productPair A B).obj X)).inv =
      (productPair A B).map (X := X) (Y := (𝟙_ (Even A × Even B)) ⊗ X) (λ_ X).inv := rfl

theorem productPair_rightUnitor_inv (X : Even A × Even B) :
    (ρ_ ((productPair A B).obj X)).inv =
      (productPair A B).map (X := X) (Y := X ⊗ (𝟙_ (Even A × Even B))) (ρ_ X).inv := rfl

def productExactPairing (X Y : Even A × Even B) [ExactPairing X.1 Y.1] [ExactPairing X.2 Y.2] :
    ExactPairing ((productPair A B).obj X) ((productPair A B).obj Y) where
  coevaluation' := (productPair A B).map (X := (𝟙_ (Even A), 𝟙_ (Even B))) (Y := X ⊗ Y) (η_ X.1 Y.1, η_ X.2 Y.2)
  evaluation' := (productPair A B).map (X := Y ⊗ X) (Y := (𝟙_ (Even A), 𝟙_ (Even B))) (ε_ X.1 Y.1, ε_ X.2 Y.2)
  coevaluation_evaluation' := by
    rw [productPair_associator_inv, productPair_rightUnitor_hom, productPair_leftUnitor_inv,
      productPair_whiskerLeft, productPair_whiskerRight, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    apply congrArg (productPair A B).map
    exact Prod.ext (ExactPairing.coevaluation_evaluation X.1 Y.1)
      (ExactPairing.coevaluation_evaluation X.2 Y.2)
  evaluation_coevaluation' := by
    rw [productPair_associator_hom, productPair_leftUnitor_hom, productPair_rightUnitor_inv,
      productPair_whiskerLeft, productPair_whiskerRight, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    apply congrArg (productPair A B).map
    exact Prod.ext (ExactPairing.evaluation_coevaluation X.1 Y.1)
      (ExactPairing.evaluation_coevaluation X.2 Y.2)

instance productRightRigid [RightRigidCategory (Even A)] [RightRigidCategory (Even B)] :
    RightRigidCategory (Even (SuperTensorProduct A B)) where
  rightDual X := {
    rightDual := (productPair A B).obj ((productFirst X)ᘁ, (productSecond X)ᘁ)
    exact := productExactPairing (productFirst X, productSecond X) _ }

instance productLeftRigid [LeftRigidCategory (Even A)] [LeftRigidCategory (Even B)] :
    LeftRigidCategory (Even (SuperTensorProduct A B)) where
  leftDual X := {
    leftDual := (productPair A B).obj (HasLeftDual.leftDual (productFirst X), HasLeftDual.leftDual (productSecond X))
    exact := productExactPairing _ (productFirst X, productSecond X) }

instance productRigid [RigidCategory (Even A)] [RigidCategory (Even B)] :
    RigidCategory (Even (SuperTensorProduct A B)) where

end RMod.BrundanEllis.Stacking
