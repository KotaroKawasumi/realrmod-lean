import RMod.Classification.Proofs.ParityCentralRoutes

/-!
# The universal signed parity pentagon

Gathering all central factors gives the same ordinary-object comparison
on both routes. The contraction-word theorem supplies the unique Koszul
sign. Real linearity moves that scalar through tensoring and composition;
cancelling the final gathering isomorphism proves the pentagon for the
actual scalar-free normalizers on arbitrary objects.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

attribute [local implicit_reducible] CategoryTheory.Center CategoryTheory.Center.tensorObj

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem parityPentagonEven_sign (W X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₃ : a + r = q + s)
    (h₄ : b + t = e + r) (h₅ : d + t = f + s) :
    (parityPentagonTwoEvenIso C p hp W X Y Z a b c d e f q r s t h₃ h₄).hom =
      ((-1 : ℝ) ^ (a * e).val) •
        (parityPentagonThreeEvenIso C p hp W X Y Z a b c d e f q r s t h₁ h₂ h₅).hom := by
  let f₁ := parityPairCompare C p hp a b c d h₁
  let f₂ := parityPairCompare C p hp c f e q h₂
  let f₃ := parityPairCompare C p hp a r q s h₃
  let f₄ := parityPairCompare C p hp b t e r h₄
  let f₅ := parityPairCompare C p hp d t f s h₅
  have hs : (CentralWord.wordTwo f₃ f₄).hom.f =
      ((-1 : ℝ) ^ (a * e).val) • (CentralWord.wordThree f₁ f₂ f₅).hom.f := by
    apply WideSubcategory.hom_ext
    change (CentralWord.wordTwo f₃ f₄).hom.f.hom =
      C.data.smul ((-1 : ℝ) ^ (a * e).val) (CentralWord.wordThree f₁ f₂ f₅).hom.f.hom
    dsimp only [f₁, f₂, f₃, f₄, f₅]
    rw [parity_wordTwo_eq C p hp a b c d e f q r s t h₃ h₄,
      parity_wordThree_eq C p hp a b c d e f q r s t h₁ h₂ h₅]
    exact parityCenter_contractionWord_sign C p hp a b c d e f q r s t h₁ h₂ h₃ h₄ h₅
  rw [parityPentagonTwoEvenIso_eq_central C p hp W X Y Z a b c d e f q r s t h₃ h₄,
    parityPentagonThreeEvenIso_eq_central C p hp W X Y Z a b c d e f q r s t h₁ h₂ h₅]
  change (CentralWord.twoRoute W X Y Z f₃ f₄).hom =
    ((-1 : ℝ) ^ (a * e).val) • (CentralWord.threeRoute W X Y Z f₁ f₂ f₅).hom
  apply (cancel_mono (CentralWord.gatherFourRight W X Y Z
    (factorCenter C p hp e) (factorCenter C p hp q) (factorCenter C p hp s)).hom).1
  rw [Linear.smul_comp, CentralWord.twoRoute_gather, CentralWord.threeRoute_gather,
    hs, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

include hp

/-- The sign equation holds for the explicit raw route data used by the
pullback, with no simplicity assumption on the four ordinary objects. -/
theorem parityPentagon_sign (W X Y Z : C.data.Obj) (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₃ : a + r = q + s)
    (h₄ : b + t = e + r) (h₅ : d + t = f + s) :
    (p.parityPentagonTwo W X Y Z a b c d e f q r s t h₃ h₄).hom =
      C.data.smul ((-1 : ℝ) ^ (a * e).val)
        (p.parityPentagonThree W X Y Z a b c d e f q r s t h₁ h₂ h₅).hom := by
  have he := congrArg (fun f => f.hom) (parityPentagonEven_sign C p hp
    (evenObj ℝ (LinearCategory C) W) (evenObj ℝ (LinearCategory C) X)
    (evenObj ℝ (LinearCategory C) Y) (evenObj ℝ (LinearCategory C) Z)
    a b c d e f q r s t h₁ h₂ h₃ h₄ h₅)
  change (parityPentagonTwoEvenIso C p hp _ _ _ _ a b c d e f q r s t h₃ h₄).hom.hom =
    C.data.smul ((-1 : ℝ) ^ (a * e).val)
      (parityPentagonThreeEvenIso C p hp _ _ _ _ a b c d e f q r s t h₁ h₂ h₅).hom.hom at he
  simp only [parityPentagonTwoEvenIso_hom, parityPentagonThreeEvenIso_hom] at he
  exact he

end RMod.Classification
