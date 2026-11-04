import RMod.Classification.Instances.EvenNormalizers

/-!
# Pentagon route expressions for Mathlib monoidal calculations

The raw twisted object is viewed in the even category, so its object
definition still uses only the original tensor operation. The two route
isomorphisms follow the same three-edge and two-edge lists as the raw
routes. Their maps will be compared before applying coherence tactics.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

abbrev twistedEvenObj (a : ZMod 2) (X Y : EvenSubcategory ℝ (LinearCategory C)) :
    EvenSubcategory ℝ (LinearCategory C) :=
  ⟨C.data.tensorObj (C.data.tensorObj X.obj Y.obj) (p.factor a)⟩

noncomputable def parityPentagonThreeEvenIso (W X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b c d e f q _r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₅ : d + t = f + s) :
    twistedEvenObj C p t (twistedEvenObj C p b (twistedEvenObj C p a W X) Y) Z ≅
      twistedEvenObj C p s W (twistedEvenObj C p q X (twistedEvenObj C p e Y Z)) :=
  let A₁ := tensorIso
    (tensorIso (scalarFreeAssociatorEvenIso C p hp W X Y a b c d h₁) (Iso.refl Z))
    (Iso.refl (evenObj ℝ (LinearCategory C) (p.factor t)))
  let A₂ := scalarFreeAssociatorEvenIso C p hp W (twistedEvenObj C p c X Y) Z d t f s h₅
  let A₃ := tensorIso
    (tensorIso (Iso.refl W) (scalarFreeAssociatorEvenIso C p hp X Y Z c f e q h₂))
    (Iso.refl (evenObj ℝ (LinearCategory C) (p.factor s)))
  (A₁ ≪≫ A₂) ≪≫ A₃

noncomputable def parityPentagonTwoEvenIso (W X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b _c _d e _f q r s t : ZMod 2) (h₃ : a + r = q + s) (h₄ : b + t = e + r) :
    twistedEvenObj C p t (twistedEvenObj C p b (twistedEvenObj C p a W X) Y) Z ≅
      twistedEvenObj C p s W (twistedEvenObj C p q X (twistedEvenObj C p e Y Z)) :=
  scalarFreeAssociatorEvenIso C p hp (twistedEvenObj C p a W X) Y Z b t e r h₄ ≪≫
    scalarFreeAssociatorEvenIso C p hp W X (twistedEvenObj C p e Y Z) a r q s h₃

end RMod.Classification
