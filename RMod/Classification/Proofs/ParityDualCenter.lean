import RMod.Classification.Instances.ParityDualCenter
import RMod.Classification.Proofs.CentralDuality
import RMod.Classification.Proofs.EvenNormalizers

/-!
# Comparing the central duality maps with their raw data

The center square contraction and both generic dual normalizers preserve
the advertised raw maps and inverses. These equalities connect the
ordinary monoidal snake computation to the pullback construction.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem factorSquareCenterIso_hom (a : ZMod 2) :
    (factorSquareCenterIso C p hp a).hom.f.hom = (p.contractEqualFactors a).hom := by
  rcases parity_cases a with rfl | rfl
  all_goals
    change C.data.comp (factorMultiplyCenterIso C p hp _ _).hom.f.hom (C.data.id _) =
      C.data.comp (p.multiplyFactors _ _).hom (C.data.id _)
    rw [factorMultiplyCenterIso_hom]
    rfl

theorem factorSquareCenterIso_inv (a : ZMod 2) :
    (factorSquareCenterIso C p hp a).inv.f.hom = (p.contractEqualFactors a).inv := by
  rcases parity_cases a with rfl | rfl
  all_goals
    change C.data.comp (C.data.id _) (factorMultiplyCenterIso C p hp _ _).inv.f.hom =
      C.data.comp (C.data.id _) (p.multiplyFactors _ _).inv
    rw [factorMultiplyCenterIso_inv]
    rfl

theorem centralPositive_hom (X Y : EvenSubcategory ℝ (LinearCategory C)) (a : ZMod 2) :
    (CentralDuality.positive X Y (factorCenter C p hp a) (factorSquareCenterIso C p hp a)).hom.hom =
      (p.dualPositiveNormalizer X.obj Y.obj a).hom := by
  change C.data.comp _ (C.data.comp _ (C.data.comp
    (C.data.tensorHom _ (factorSquareCenterIso C p hp a).hom.f.hom) _)) = _
  rw [factorSquareCenterIso_hom]
  simp only [PiData.dualPositiveNormalizer, PiData.eraseFactorPair, IsoData.trans,
    IsoData.tensor, IsoData.symm, IsoData.assoc, IsoData.refl, IsoData.rightUnit, C.laws.comp_assoc]
  rfl

theorem centralPositive_inv (X Y : EvenSubcategory ℝ (LinearCategory C)) (a : ZMod 2) :
    (CentralDuality.positive X Y (factorCenter C p hp a) (factorSquareCenterIso C p hp a)).inv.hom =
      (p.dualPositiveNormalizer X.obj Y.obj a).inv := by
  change C.data.comp (C.data.comp (C.data.comp _
    (C.data.tensorHom _ (factorSquareCenterIso C p hp a).inv.f.hom)) _) _ = _
  rw [factorSquareCenterIso_inv]
  simp only [PiData.dualPositiveNormalizer, PiData.eraseFactorPair, IsoData.trans,
    IsoData.tensor, IsoData.symm, IsoData.assoc, IsoData.refl, IsoData.rightUnit, C.laws.comp_assoc]
  rfl

theorem centralNegative_hom (X Y : EvenSubcategory ℝ (LinearCategory C)) (a : ZMod 2) :
    (CentralDuality.negative X Y (factorCenter C p hp a) (factorSquareCenterIso C p hp a)).hom.hom =
      (p.dualNegativeNormalizer X.obj Y.obj a).hom := by
  change C.data.comp (C.data.tensorHom (C.data.comp _ (C.data.comp
    (C.data.tensorHom _ ((factorHalfBraiding C p hp a).β X).hom.hom) _)) _)
    (C.data.comp _ (C.data.comp (C.data.tensorHom _ (factorSquareCenterIso C p hp a).hom.f.hom) _)) = _
  rw [factorSquareCenterIso_hom, factorHalfBraiding_hom]
  simp only [PiData.dualNegativeNormalizer, PiData.eraseFactorPair, IsoData.trans,
    IsoData.tensor, IsoData.symm, IsoData.assoc, IsoData.refl, IsoData.rightUnit, C.laws.comp_assoc]
  rfl

end RMod.Classification
