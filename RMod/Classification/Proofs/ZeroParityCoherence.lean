import RMod.Classification.Proofs.EvenNormalizers
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Unit-only specialization of the normalizer

When all parity values vanish, the specified local associator is the
canonical unitor/associator composite. Mathlib monoidal coherence proves
the equality of the full lists of structural maps. This also checks that
the right-parity convention retains the ordinary associator normalization.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem moveFactorEven_zero (X : EvenSubcategory ℝ (LinearCategory C)) :
    IsoData.toEvenIso C (p.moveFactor 0 X.obj) (hp.moveFactor_evenIso C.laws 0 X.obj) =
      (λ_ X) ≪≫ (ρ_ X).symm := rfl

theorem multiplyFactorsEven_zero :
    IsoData.toEvenIso C (p.multiplyFactors 0 0) (hp.multiplyFactors_evenIso C.laws 0 0) =
      λ_ (𝟙_ (EvenSubcategory ℝ (LinearCategory C))) := rfl

theorem scalarFreeAssociatorEven_zero (X Y Z : EvenSubcategory ℝ (LinearCategory C)) :
    (scalarFreeAssociatorEvenIso C p hp X Y Z 0 0 0 0 rfl).hom =
      (tensorIso (tensorIso (ρ_ (X ⊗ Y)) (Iso.refl Z))
        (Iso.refl (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))) ≪≫
      (tensorIso (α_ X Y Z) (Iso.refl (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))) ≪≫
        tensorIso (tensorIso (Iso.refl X) (ρ_ (Y ⊗ Z)).symm)
          (Iso.refl (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))))).hom := by
  unfold scalarFreeAssociatorEvenIso normalLeftEvenIso normalRightEvenIso
  rw [moveFactorEven_zero C p hp, multiplyFactorsEven_zero C p hp]
  simp only [eqToIso_refl]
  monoidal_coherence

end RMod.Classification
