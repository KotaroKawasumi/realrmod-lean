import RMod.Classification.Proofs.ParityFactorCenter
import RMod.Classification.Proofs.ParityCrossing

/-!
# Associative parity multiplication and its braiding in Mathlib's center

The raw multiplication coherence transfers to the actual center maps,
including the transport of the parity sum. Forgetting the center braiding
recovers the specified moveFactor map, so its multiplication comparison
has exactly the already proved Koszul sign.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory BraidedCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem center_eqToHom {X Y : Center (EvenSubcategory ℝ (LinearCategory C))} (he : X = Y) :
    (eqToHom he).f.hom = (IsoData.ofEq C.data (congrArg (fun T => T.1.obj) he)).hom := by
  subst Y
  rfl

theorem factorMultiplyCenter_assoc (a b c : ZMod 2) :
    ((factorMultiplyCenterIso C p hp a b).hom ⊗ₘ 𝟙 (factorCenter C p hp c)) ≫
        (factorMultiplyCenterIso C p hp (a + b) c).hom ≫
          eqToHom (congrArg (factorCenter C p hp) (add_assoc a b c)) =
      (α_ (factorCenter C p hp a) (factorCenter C p hp b) (factorCenter C p hp c)).hom ≫
        (𝟙 (factorCenter C p hp a) ⊗ₘ (factorMultiplyCenterIso C p hp b c).hom) ≫
          (factorMultiplyCenterIso C p hp a (b + c)).hom := by
  apply Center.ext
  apply WideSubcategory.hom_ext
  change C.data.comp (C.data.tensorHom (p.multiplyFactors a b).hom (C.data.id (p.factor c)))
    (C.data.comp (p.multiplyFactors (a + b) c).hom
      (eqToHom (congrArg (factorCenter C p hp) (add_assoc a b c))).f.hom) =
    C.data.comp (C.data.associatorHom (p.factor a) (p.factor b) (p.factor c))
      (C.data.comp (C.data.tensorHom (C.data.id (p.factor a)) (p.multiplyFactors b c).hom)
        (p.multiplyFactors a (b + c)).hom)
  rw [center_eqToHom]
  rw [← C.laws.comp_assoc]
  exact hp.multiplyFactors_assoc C.laws a b c

theorem factorCenter_braiding_hom (a b : ZMod 2) :
    (β_ (factorCenter C p hp a) (factorCenter C p hp b)).hom.f.hom =
      (p.moveFactor a (p.factor b)).hom :=
  factorHalfBraiding_hom C p hp a (evenObj ℝ (LinearCategory C) (p.factor b))

theorem factorMultiplyCenter_braiding (a b : ZMod 2) :
    ((β_ (factorCenter C p hp a) (factorCenter C p hp b)).hom ≫
      (factorMultiplyCenterIso C p hp b a).hom).f.hom =
    C.data.smul ((-1 : ℝ) ^ (a * b).val)
      (((factorMultiplyCenterIso C p hp a b).hom ≫
        eqToHom (congrArg (factorCenter C p hp) (add_comm a b))).f.hom) := by
  change C.data.comp (β_ (factorCenter C p hp a) (factorCenter C p hp b)).hom.f.hom
    (p.multiplyFactors b a).hom =
    C.data.smul ((-1 : ℝ) ^ (a * b).val)
      (C.data.comp (p.multiplyFactors a b).hom
        (eqToHom (congrArg (factorCenter C p hp) (add_comm a b))).f.hom)
  rw [factorCenter_braiding_hom, center_eqToHom]
  exact hp.moveFactor_multiply C.laws a b

end RMod.Classification
