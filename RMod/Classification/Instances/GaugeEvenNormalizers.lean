import RMod.Classification.Proofs.GaugeLocalNormalizers
import RMod.Classification.Instances.EvenIsos

/-!
# The gauge words as explicit Mathlib monoidal expressions

The underlying maps are the already specified raw gauge normalizers.
Their structural expressions remain visible here so that ordinary
monoidal coherence applies without changing the actual tensorator.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

noncomputable def rightFactorPairNormalizerEvenIso (X : EvenSubcategory ℝ (LinearCategory C))
    (a b : ZMod 2) :
    (X ⊗ evenObj ℝ (LinearCategory C) (p.factor a)) ⊗ evenObj ℝ (LinearCategory C) (p.factor b) ≅
      X ⊗ evenObj ℝ (LinearCategory C) (p.factor (a + b)) :=
  (α_ X (evenObj ℝ (LinearCategory C) (p.factor a)) (evenObj ℝ (LinearCategory C) (p.factor b))) ≪≫
    tensorIso (CategoryTheory.Iso.refl X)
      (IsoData.toEvenIso C (p.multiplyFactors a b) (hp.multiplyFactors_evenIso C.laws a b))

noncomputable def rightFactorTensorNormalizerEvenIso (X Y : EvenSubcategory ℝ (LinearCategory C))
    (a b : ZMod 2) :
    (X ⊗ evenObj ℝ (LinearCategory C) (p.factor a)) ⊗
        (Y ⊗ evenObj ℝ (LinearCategory C) (p.factor b)) ≅
      (X ⊗ Y) ⊗ evenObj ℝ (LinearCategory C) (p.factor (a + b)) :=
  let P := evenObj ℝ (LinearCategory C) (p.factor a)
  let Q := evenObj ℝ (LinearCategory C) (p.factor b)
  let i₁ := (α_ (X ⊗ P) Y Q).symm
  let i₂ := tensorIso (α_ X P Y) (CategoryTheory.Iso.refl Q)
  let i₃ := tensorIso (tensorIso (CategoryTheory.Iso.refl X)
    (IsoData.toEvenIso C (p.moveFactor a Y.obj) (hp.moveFactor_evenIso C.laws a Y.obj)))
    (CategoryTheory.Iso.refl Q)
  let i₄ := tensorIso (α_ X Y P).symm (CategoryTheory.Iso.refl Q)
  (((i₁ ≪≫ i₂) ≪≫ i₃) ≪≫ i₄) ≪≫ rightFactorPairNormalizerEvenIso C p hp (X ⊗ Y) a b

noncomputable def gaugeSourceNormalizerEvenIso (X Y : EvenSubcategory ℝ (LinearCategory C))
    (a b n' : ZMod 2) :
    ((X ⊗ evenObj ℝ (LinearCategory C) (p.factor a)) ⊗
        (Y ⊗ evenObj ℝ (LinearCategory C) (p.factor b))) ⊗
        evenObj ℝ (LinearCategory C) (p.factor n') ≅
      (X ⊗ Y) ⊗ evenObj ℝ (LinearCategory C) (p.factor ((a + b) + n')) :=
  tensorIso (rightFactorTensorNormalizerEvenIso C p hp X Y a b)
      (CategoryTheory.Iso.refl (evenObj ℝ (LinearCategory C) (p.factor n'))) ≪≫
    rightFactorPairNormalizerEvenIso C p hp (X ⊗ Y) (a + b) n'

noncomputable def scalarFreeGaugeEvenIso (X Y : EvenSubcategory ℝ (LinearCategory C))
    (a b n' n c : ZMod 2) (he : (a + b) + n' = n + c) :
    ((X ⊗ evenObj ℝ (LinearCategory C) (p.factor a)) ⊗
        (Y ⊗ evenObj ℝ (LinearCategory C) (p.factor b))) ⊗
        evenObj ℝ (LinearCategory C) (p.factor n') ≅
      ((X ⊗ Y) ⊗ evenObj ℝ (LinearCategory C) (p.factor n)) ⊗
        evenObj ℝ (LinearCategory C) (p.factor c) :=
  gaugeSourceNormalizerEvenIso C p hp X Y a b n' ≪≫
    (eqToIso (congrArg (fun z => (X ⊗ Y) ⊗ evenObj ℝ (LinearCategory C) (p.factor z)) he) ≪≫
      (rightFactorPairNormalizerEvenIso C p hp (X ⊗ Y) n c).symm)

end RMod.Classification
