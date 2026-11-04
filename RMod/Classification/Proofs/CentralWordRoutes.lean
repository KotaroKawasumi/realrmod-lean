import RMod.Classification.Instances.CentralWordRoutes
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Gathering the ordinary-object pentagon

Naturality of a center map moves a pair replacement past an ordinary
object. Interchange then separates the ordinary-object crossings from
the central contraction word. These arguments are independent of parity
labels and of the concrete category used for the classification.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.CentralWord

open CategoryTheory MonoidalCategory BraidedCategory

attribute [local implicit_reducible] CategoryTheory.Center
  CategoryTheory.Center.tensorObj

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- The central tensor product crosses an ordinary object one factor at
 a time, in the order determined by its half-braiding. -/
theorem tensor_crossing (A B : Center V) (Z : V) :
    ((A ⊗ B).2.β Z).hom =
      (α_ A.1 B.1 Z).hom ≫ (A.1 ◁ (B.2.β Z).hom) ≫
        (α_ A.1 Z B.1).inv ≫ ((A.2.β Z).hom ▷ B.1) ≫ (α_ Z A.1 B.1).hom := rfl

/-- Gathering the longer route produces exactly its three-factor word. -/
theorem threeRoute_gather (W X Y Z : V) {A B C D E F Q S T : Center V}
    (f₁ : A ⊗ B ≅ C ⊗ D) (f₂ : C ⊗ F ≅ E ⊗ Q) (f₅ : D ⊗ T ≅ F ⊗ S) :
    (threeRoute W X Y Z f₁ f₂ f₅).hom ≫ (gatherFourRight W X Y Z E Q S).hom =
      (gatherFourLeft W X Y Z A B T).hom ≫
        ((W ⊗ (X ⊗ (Y ⊗ Z))) ◁ (wordThree f₁ f₂ f₅).hom.f) := by
  let x₁ : A.1 ⊗ B.1 ⟶ C.1 ⊗ D.1 := f₁.hom.f
  let x₂ : C.1 ⊗ F.1 ⟶ E.1 ⊗ Q.1 := f₂.hom.f
  let x₅ : D.1 ⊗ T.1 ⟶ F.1 ⊗ S.1 := f₅.hom.f
  let bCD : (C.1 ⊗ D.1) ⊗ Z ⟶ Z ⊗ (C.1 ⊗ D.1) := ((C ⊗ D).2.β Z).hom
  have hCD : bCD = (α_ C.1 D.1 Z).hom ≫ (C.1 ◁ (D.2.β Z).hom) ≫
      (α_ C.1 Z D.1).inv ≫ ((C.2.β Z).hom ▷ D.1) ≫ (α_ Z C.1 D.1).hom :=
    tensor_crossing C D Z
  calc
    _ = 𝟙 ((((((W ⊗ X) ⊗ A.1) ⊗ Y) ⊗ B.1) ⊗ Z) ⊗ T.1) ⊗≫
      ((W ⊗ X) ◁ (A.2.β Y).hom) ▷ B.1 ▷ Z ▷ T.1 ⊗≫
      ((W ⊗ (X ⊗ Y)) ◁ x₁) ▷ Z ▷ T.1 ⊗≫
      ((W ⊗ (X ⊗ Y)) ◁ C.1 ◁ (D.2.β Z).hom) ▷ T.1 ⊗≫
      (W ⊗ (X ⊗ Y)) ◁ ((C.1 ⊗ Z) ◁ x₅ ≫ (C.2.β Z).hom ▷ (F.1 ⊗ S.1)) ⊗≫
      ((W ⊗ (X ⊗ (Y ⊗ Z))) ◁ x₂) ▷ S.1 ⊗≫ 𝟙 ((W ⊗ (X ⊗ (Y ⊗ Z))) ⊗ ((E.1 ⊗ Q.1) ⊗ S.1)) := by
        simp only [threeRoute, localMove, gatherLeft, gatherRight, gatherFourRight,
          Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, tensorIso_hom, tensorIso_inv,
          Iso.refl_hom, Iso.refl_inv, Functor.mapIso_hom,
          Center.forget_map]
        monoidal
    _ = 𝟙 ((((((W ⊗ X) ⊗ A.1) ⊗ Y) ⊗ B.1) ⊗ Z) ⊗ T.1) ⊗≫
      ((W ⊗ X) ◁ (A.2.β Y).hom) ▷ B.1 ▷ Z ▷ T.1 ⊗≫
      ((W ⊗ (X ⊗ Y)) ◁ (x₁ ▷ Z ≫ bCD)) ▷ T.1 ⊗≫
      (W ⊗ (X ⊗ (Y ⊗ Z))) ◁ C.1 ◁ x₅ ⊗≫ ((W ⊗ (X ⊗ (Y ⊗ Z))) ◁ x₂) ▷ S.1 ⊗≫ 𝟙 ((W ⊗ (X ⊗ (Y ⊗ Z))) ⊗ ((E.1 ⊗ Q.1) ⊗ S.1)) := by
        rw [whisker_exchange, hCD]
        monoidal
    _ = _ := by
      dsimp only [x₁, x₂, x₅, bCD]
      rw [f₁.hom.comm]
      simp only [gatherFourLeft, gatherLeft, wordThree, Iso.trans_hom, Iso.symm_hom,
        tensorIso_hom, Iso.refl_hom, Center.comp_f, Center.tensor_f,
        Center.associator_hom_f, Center.associator_inv_f, Center.id_f]
      monoidal

/-- Gathering the shorter route exposes one actual center braiding. -/
theorem twoRoute_gather (W X Y Z : V) {A B E Q R S T : Center V}
    (f₃ : A ⊗ R ≅ Q ⊗ S) (f₄ : B ⊗ T ≅ E ⊗ R) :
    (twoRoute W X Y Z f₃ f₄).hom ≫ (gatherFourRight W X Y Z E Q S).hom =
      (gatherFourLeft W X Y Z A B T).hom ≫
        ((W ⊗ (X ⊗ (Y ⊗ Z))) ◁ (wordTwo f₃ f₄).hom.f) := by
  let x₃ : A.1 ⊗ R.1 ⟶ Q.1 ⊗ S.1 := f₃.hom.f
  let x₄ : B.1 ⊗ T.1 ⟶ E.1 ⊗ R.1 := f₄.hom.f
  have hb : (β_ A E).hom.f = (A.2.β E.1).hom := rfl
  calc
    _ = 𝟙 ((((((W ⊗ X) ⊗ A.1) ⊗ Y) ⊗ B.1) ⊗ Z) ⊗ T.1) ⊗≫
      ((((W ⊗ X) ⊗ A.1) ⊗ Y) ◁ (B.2.β Z).hom) ▷ T.1 ⊗≫
      (W ⊗ X) ◁ ((A.1 ⊗ (Y ⊗ Z)) ◁ x₄ ≫ (A.2.β (Y ⊗ Z)).hom ▷ (E.1 ⊗ R.1)) ⊗≫
      ((W ⊗ (X ⊗ (Y ⊗ Z))) ◁ (A.2.β E.1).hom) ▷ R.1 ⊗≫
      (W ⊗ (X ⊗ (Y ⊗ Z))) ◁ E.1 ◁ x₃ ⊗≫
      𝟙 ((W ⊗ (X ⊗ (Y ⊗ Z))) ⊗ ((E.1 ⊗ Q.1) ⊗ S.1)) := by
        simp only [twoRoute, localMove, gatherLeft, gatherRight, gatherFourRight,
          Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, tensorIso_hom, tensorIso_inv,
          Iso.refl_hom, Iso.refl_inv, Functor.mapIso_hom, Center.forget_map,
          A.2.monoidal (Y ⊗ Z) E.1]
        monoidal
    _ = 𝟙 ((((((W ⊗ X) ⊗ A.1) ⊗ Y) ⊗ B.1) ⊗ Z) ⊗ T.1) ⊗≫
      ((W ⊗ X) ◁ ((A.1 ⊗ Y) ◁ (B.2.β Z).hom ≫
        (A.2.β Y).hom ▷ (Z ⊗ B.1))) ▷ T.1 ⊗≫
      ((W ⊗ (X ⊗ Y)) ◁ (A.2.β Z).hom) ▷ B.1 ▷ T.1 ⊗≫
      (W ⊗ (X ⊗ (Y ⊗ Z))) ◁ A.1 ◁ x₄ ⊗≫
      ((W ⊗ (X ⊗ (Y ⊗ Z))) ◁ (A.2.β E.1).hom) ▷ R.1 ⊗≫
      (W ⊗ (X ⊗ (Y ⊗ Z))) ◁ E.1 ◁ x₃ ⊗≫
      𝟙 ((W ⊗ (X ⊗ (Y ⊗ Z))) ⊗ ((E.1 ⊗ Q.1) ⊗ S.1)) := by
        rw [whisker_exchange]
        simp only [A.2.monoidal Y Z]
        monoidal
    _ = _ := by
      rw [whisker_exchange]
      simp only [gatherFourLeft, gatherLeft, wordTwo, Iso.trans_hom, Iso.symm_hom,
        tensorIso_hom, Iso.refl_hom, Center.comp_f, Center.tensor_f,
        Center.associator_hom_f, Center.associator_inv_f, Center.id_f, hb, tensor_crossing]
      monoidal

end RMod.Classification.CentralWord
