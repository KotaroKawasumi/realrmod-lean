import RMod.Classification.Instances.EvenPentagonRoutes
import RMod.Classification.Proofs.EvenNormalizers
import RMod.Classification.Proofs.ParityPentagonRoutes

/-!
# The Mathlib route expressions are the actual raw route maps

These identities transfer monoidal calculations back to the explicit
construction. The scalar-one local associator comparison is applied at
each edge; no pentagon equation is assumed by either route definition.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem parityPentagonThreeEvenIso_hom (W X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₅ : d + t = f + s) :
    (parityPentagonThreeEvenIso C p hp W X Y Z a b c d e f q r s t h₁ h₂ h₅).hom.hom =
      (p.parityPentagonThree W.obj X.obj Y.obj Z.obj a b c d e f q r s t h₁ h₂ h₅).hom := by
  change C.data.comp
    (C.data.comp
      (C.data.tensorHom (C.data.tensorHom
        (scalarFreeAssociatorEvenIso C p hp W X Y a b c d h₁).hom.hom (C.data.id Z.obj))
        (C.data.id (p.factor t)))
      (scalarFreeAssociatorEvenIso C p hp W (twistedEvenObj C p c X Y) Z d t f s h₅).hom.hom)
    (C.data.tensorHom (C.data.tensorHom (C.data.id W.obj)
      (scalarFreeAssociatorEvenIso C p hp X Y Z c f e q h₂).hom.hom) (C.data.id (p.factor s))) = _
  simp only [scalarFreeAssociatorEvenIso_hom]
  rfl

theorem parityPentagonTwoEvenIso_hom (W X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b c d e f q r s t : ZMod 2) (h₃ : a + r = q + s) (h₄ : b + t = e + r) :
    (parityPentagonTwoEvenIso C p hp W X Y Z a b c d e f q r s t h₃ h₄).hom.hom =
      (p.parityPentagonTwo W.obj X.obj Y.obj Z.obj a b c d e f q r s t h₃ h₄).hom := by
  change C.data.comp
    (scalarFreeAssociatorEvenIso C p hp (twistedEvenObj C p a W X) Y Z b t e r h₄).hom.hom
    (scalarFreeAssociatorEvenIso C p hp W X (twistedEvenObj C p e Y Z) a r q s h₃).hom.hom = _
  simp only [scalarFreeAssociatorEvenIso_hom]
  rfl

end RMod.Classification
