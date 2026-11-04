import RMod.Classification.Instances.CentralWordNormalizers

/-!
# Pentagon routes with arbitrary central pair comparisons

Separate the ordinary objects from the central factors. The comparison
maps on the factors are retained explicitly, including the actual
braiding in the shorter route. The next proofs gather ordinary objects
to identify these routes with the corresponding three-factor words.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.CentralWord

open CategoryTheory MonoidalCategory BraidedCategory

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

noncomputable def wordThree {A B C D E F Q S T : Center V}
    (f₁ : A ⊗ B ≅ C ⊗ D) (f₂ : C ⊗ F ≅ E ⊗ Q) (f₅ : D ⊗ T ≅ F ⊗ S) :
    (A ⊗ B) ⊗ T ≅ (E ⊗ Q) ⊗ S :=
  tensorIso f₁ (Iso.refl T) ≪≫ α_ C D T ≪≫ tensorIso (Iso.refl C) f₅ ≪≫
    (α_ C F S).symm ≪≫ tensorIso f₂ (Iso.refl S)

noncomputable def wordTwo {A B E Q R S T : Center V}
    (f₃ : A ⊗ R ≅ Q ⊗ S) (f₄ : B ⊗ T ≅ E ⊗ R) :
    (A ⊗ B) ⊗ T ≅ (E ⊗ Q) ⊗ S :=
  α_ A B T ≪≫ tensorIso (Iso.refl A) f₄ ≪≫ (α_ A E R).symm ≪≫
    tensorIso (β_ A E) (Iso.refl R) ≪≫ α_ E A R ≪≫
      tensorIso (Iso.refl E) f₃ ≪≫ (α_ E Q S).symm

noncomputable def threeRoute (W X Y Z : V) {A B C D E F Q S T : Center V}
    (f₁ : A ⊗ B ≅ C ⊗ D) (f₂ : C ⊗ F ≅ E ⊗ Q) (f₅ : D ⊗ T ≅ F ⊗ S) :
    (((((W ⊗ X) ⊗ A.1) ⊗ Y) ⊗ B.1) ⊗ Z) ⊗ T.1 ≅
      (W ⊗ ((X ⊗ ((Y ⊗ Z) ⊗ E.1)) ⊗ Q.1)) ⊗ S.1 :=
  tensorIso (tensorIso (localMove W X Y f₁) (Iso.refl Z)) (Iso.refl T.1) ≪≫
    localMove W ((X ⊗ Y) ⊗ C.1) Z f₅ ≪≫
      tensorIso (tensorIso (Iso.refl W) (localMove X Y Z f₂)) (Iso.refl S.1)

noncomputable def twoRoute (W X Y Z : V) {A B E Q R S T : Center V}
    (f₃ : A ⊗ R ≅ Q ⊗ S) (f₄ : B ⊗ T ≅ E ⊗ R) :
    (((((W ⊗ X) ⊗ A.1) ⊗ Y) ⊗ B.1) ⊗ Z) ⊗ T.1 ≅
      (W ⊗ ((X ⊗ ((Y ⊗ Z) ⊗ E.1)) ⊗ Q.1)) ⊗ S.1 :=
  localMove ((W ⊗ X) ⊗ A.1) Y Z f₄ ≪≫ localMove W X ((Y ⊗ Z) ⊗ E.1) f₃

end RMod.Classification.CentralWord
