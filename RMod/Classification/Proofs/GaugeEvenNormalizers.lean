import RMod.Classification.Instances.GaugeEvenNormalizers
import RMod.Classification.Proofs.EvenNormalizers

/-! # The even gauge expressions retain the prescribed raw maps -/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem rightFactorPairNormalizerEvenIso_hom (X : EvenSubcategory ℝ (LinearCategory C)) (a b : ZMod 2) :
    (rightFactorPairNormalizerEvenIso C p hp X a b).hom.hom =
      (p.rightFactorPairNormalizer X.obj a b).hom := rfl

theorem rightFactorTensorNormalizerEvenIso_hom (X Y : EvenSubcategory ℝ (LinearCategory C)) (a b : ZMod 2) :
    (rightFactorTensorNormalizerEvenIso C p hp X Y a b).hom.hom =
      (p.rightFactorTensorNormalizer X.obj Y.obj a b).hom := rfl

theorem gaugeSourceNormalizerEvenIso_hom (X Y : EvenSubcategory ℝ (LinearCategory C)) (a b n' : ZMod 2) :
    (gaugeSourceNormalizerEvenIso C p hp X Y a b n').hom.hom =
      (p.gaugeSourceNormalizer X.obj Y.obj a b n').hom := rfl

theorem scalarFreeGaugeEvenIso_hom (X Y : EvenSubcategory ℝ (LinearCategory C))
    (a b n' n c : ZMod 2) (he : (a + b) + n' = n + c) :
    (scalarFreeGaugeEvenIso C p hp X Y a b n' n c he).hom.hom =
      (p.gaugeLocalTensorator X.obj Y.obj a b n' n c he 1).hom := by
  change C.data.comp (p.gaugeSourceNormalizer X.obj Y.obj a b n').hom
    (C.data.comp (eqToIso (congrArg (fun z => (X ⊗ Y) ⊗
      evenObj ℝ (LinearCategory C) (p.factor z)) he)).hom.hom
      (p.rightFactorPairNormalizer (C.data.tensorObj X.obj Y.obj) n c).inv) =
    C.data.smul 1 (C.data.comp (p.gaugeSourceNormalizer X.obj Y.obj a b n').hom
      (C.data.comp (IsoData.ofEq C.data _).hom
        (p.rightFactorPairNormalizer (C.data.tensorObj X.obj Y.obj) n c).inv))
  rw [C.laws.one_smul]
  congr 2
  exact even_eqToIso_hom C _

end RMod.Classification
