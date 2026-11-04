import RMod.Classification.Proofs.ParityFactorCenter
import RMod.Classification.Instances.ParityDualNormalizers
import RMod.Classification.Instances.CentralDuality

/-!
# The actual square contraction in the center

The contraction of two equal parity factors is their existing central
multiplication followed by the equality a+a=0. Thus the generic central
duality calculation applies to the specified parity data.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

noncomputable def factorSquareCenterIso (a : ZMod 2) :
    factorCenter C p hp a ⊗ factorCenter C p hp a ≅
      𝟙_ (Center (EvenSubcategory ℝ (LinearCategory C))) :=
  factorMultiplyCenterIso C p hp a a ≪≫
    eqToIso (congrArg (factorCenter C p hp) (CharTwo.add_self_eq_zero a))

end RMod.Classification
