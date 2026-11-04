import RMod.Classification.Proofs.GaugeEvenNormalizers
import RMod.Classification.Proofs.ParityDualSnake

/-!
# The local unit diagrams for the specified gauge tensorator

The normalized unit input has zero shift and zero binary parity. The
surviving shift may be either parity. Expanding the actual normalizers
then leaves only associators and unitors, so Mathlib monoidal coherence
proves the complete diagram, including the inserted unit comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

attribute [local implicit_reducible] PiData.factor

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem scalarFreeGaugeEven_left_unit (Y : EvenSubcategory ℝ (LinearCategory C)) (a : ZMod 2) :
    (((ρ_ (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))).inv ⊗ₘ
      𝟙 (Y ⊗ evenObj ℝ (LinearCategory C) (p.factor a))) ⊗ₘ
      𝟙 (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))) ≫
      (scalarFreeGaugeEvenIso C p hp (𝟙_ (EvenSubcategory ℝ (LinearCategory C))) Y
        0 a 0 0 a (by simp)).hom ≫
      (((ρ_ ((𝟙_ (EvenSubcategory ℝ (LinearCategory C))) ⊗ Y)).hom ≫ (λ_ Y).hom) ⊗ₘ
        𝟙 (evenObj ℝ (LinearCategory C) (p.factor a))) =
      (ρ_ ((𝟙_ (EvenSubcategory ℝ (LinearCategory C))) ⊗
        (Y ⊗ evenObj ℝ (LinearCategory C) (p.factor a)))).hom ≫
        (λ_ (Y ⊗ evenObj ℝ (LinearCategory C) (p.factor a))).hom := by
  rcases parity_cases a with rfl | rfl
  · unfold scalarFreeGaugeEvenIso gaugeSourceNormalizerEvenIso
      rightFactorTensorNormalizerEvenIso rightFactorPairNormalizerEvenIso
    dsimp only
    erw [moveFactorEven_zero C p hp, multiplyFactorsEven_zero C p hp]
    erw [eqToIso_refl]
    dsimp only [PiData.factor]
    monoidal_coherence
  · unfold scalarFreeGaugeEvenIso gaugeSourceNormalizerEvenIso
      rightFactorTensorNormalizerEvenIso rightFactorPairNormalizerEvenIso
    dsimp only
    erw [moveFactorEven_zero C p hp, multiplyFactorsEven_zero_one C p hp,
      multiplyFactorsEven_one_zero C p hp]
    erw [eqToIso_refl]
    dsimp only [PiData.factor]
    monoidal_coherence

theorem moveFactorEven_unit (a : ZMod 2) :
    IsoData.toEvenIso C (p.moveFactor a C.data.tensorUnit)
      (hp.moveFactor_evenIso C.laws a C.data.tensorUnit) =
      (ρ_ (evenObj ℝ (LinearCategory C) (p.factor a))) ≪≫
        (λ_ (evenObj ℝ (LinearCategory C) (p.factor a))).symm := by
  rcases parity_cases a with rfl | rfl
  · erw [moveFactorEven_zero C p hp (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))]
    apply CategoryTheory.Iso.ext
    monoidal_coherence
  · apply CategoryTheory.Iso.ext
    apply WideSubcategory.hom_ext
    exact hp.central_unit C.laws

theorem scalarFreeGaugeEven_right_unit (X : EvenSubcategory ℝ (LinearCategory C)) (a : ZMod 2) :
    ((𝟙 (X ⊗ evenObj ℝ (LinearCategory C) (p.factor a)) ⊗ₘ
      (ρ_ (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))).inv) ⊗ₘ
      𝟙 (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))) ≫
      (scalarFreeGaugeEvenIso C p hp X (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))
        a 0 0 0 a (by simp)).hom ≫
      (((ρ_ (X ⊗ (𝟙_ (EvenSubcategory ℝ (LinearCategory C))))).hom ≫ (ρ_ X).hom) ⊗ₘ
        𝟙 (evenObj ℝ (LinearCategory C) (p.factor a))) =
      (ρ_ ((X ⊗ evenObj ℝ (LinearCategory C) (p.factor a)) ⊗
        (𝟙_ (EvenSubcategory ℝ (LinearCategory C))))).hom ≫
        (ρ_ (X ⊗ evenObj ℝ (LinearCategory C) (p.factor a))).hom := by
  rcases parity_cases a with rfl | rfl
  · unfold scalarFreeGaugeEvenIso gaugeSourceNormalizerEvenIso
      rightFactorTensorNormalizerEvenIso rightFactorPairNormalizerEvenIso
    dsimp only
    erw [moveFactorEven_unit C p hp, multiplyFactorsEven_zero C p hp]
    erw [eqToIso_refl]
    dsimp only [PiData.factor]
    monoidal_coherence
  · unfold scalarFreeGaugeEvenIso gaugeSourceNormalizerEvenIso
      rightFactorTensorNormalizerEvenIso rightFactorPairNormalizerEvenIso
    dsimp only
    erw [moveFactorEven_unit C p hp, multiplyFactorsEven_one_zero C p hp,
      multiplyFactorsEven_zero_one C p hp]
    erw [eqToIso_refl]
    dsimp only [PiData.factor]
    monoidal_coherence

end RMod.Classification
