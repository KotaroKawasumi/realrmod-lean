import RMod.Classification.Proofs.ZeroParityCoherence
import RMod.Classification.Proofs.EvenPentagonRoutes

/-!
# The complete parity pentagon when all parity entries vanish

Every edge is the canonical unitor/associator composite. Mathlib coherence
then proves equality of both complete routes, and the route comparison
lemmas transfer the result to the actual raw normalizer expressions.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem twistedEvenObj_zero (X Y : EvenSubcategory ℝ (LinearCategory C)) :
    twistedEvenObj C p 0 X Y = (X ⊗ Y) ⊗ 𝟙_ (EvenSubcategory ℝ (LinearCategory C)) := rfl

theorem factorEven_zero : evenObj ℝ (LinearCategory C) (p.factor 0) =
    𝟙_ (EvenSubcategory ℝ (LinearCategory C)) := rfl

theorem parityPentagonEven_zero (W X Y Z : EvenSubcategory ℝ (LinearCategory C)) :
    (parityPentagonTwoEvenIso C p hp W X Y Z 0 0 0 0 0 0 0 0 0 0 rfl rfl).hom =
      (parityPentagonThreeEvenIso C p hp W X Y Z 0 0 0 0 0 0 0 0 0 0 rfl rfl rfl).hom := by
  unfold parityPentagonTwoEvenIso parityPentagonThreeEvenIso
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, scalarFreeAssociatorEven_zero C p hp]
  simp only [twistedEvenObj_zero C p, factorEven_zero C p]
  monoidal_coherence

include hp

theorem parityPentagon_zero (W X Y Z : C.data.Obj) :
    (p.parityPentagonTwo W X Y Z 0 0 0 0 0 0 0 0 0 0 rfl rfl).hom =
      (p.parityPentagonThree W X Y Z 0 0 0 0 0 0 0 0 0 0 rfl rfl rfl).hom := by
  have he := congrArg (fun f => f.hom) (parityPentagonEven_zero C p hp
    (evenObj ℝ (LinearCategory C) W) (evenObj ℝ (LinearCategory C) X)
    (evenObj ℝ (LinearCategory C) Y) (evenObj ℝ (LinearCategory C) Z))
  simp only [parityPentagonTwoEvenIso_hom, parityPentagonThreeEvenIso_hom] at he
  exact he

end RMod.Classification
