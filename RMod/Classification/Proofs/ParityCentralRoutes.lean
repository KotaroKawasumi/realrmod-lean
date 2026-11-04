import RMod.Classification.Proofs.ParityCentralNormalizers
import RMod.Classification.Proofs.EvenPentagonRoutes
import RMod.Classification.Instances.ParityPairComparison

/-!
# Exact comparison of the full parity routes and their central words

Each local normalizer is the center pair comparison proved previously.
The full route comparisons therefore preserve the specified object maps,
parentheses and inverse maps. The central words are also exactly those
whose fermionic discrepancy has already been computed.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem parityPentagonThreeEvenIso_eq_central (W X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₅ : d + t = f + s) :
    parityPentagonThreeEvenIso C p hp W X Y Z a b c d e f q r s t h₁ h₂ h₅ =
      CentralWord.threeRoute W X Y Z
        (parityPairCompare C p hp a b c d h₁)
        (parityPairCompare C p hp c f e q h₂)
        (parityPairCompare C p hp d t f s h₅) := by
  unfold parityPentagonThreeEvenIso CentralWord.threeRoute
  simp only [scalarFreeAssociatorEvenIso_eq_central C p hp]
  apply Iso.ext
  simp only [Iso.trans_hom, Category.assoc]
  rfl

theorem parityPentagonTwoEvenIso_eq_central (W X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b c d e f q r s t : ZMod 2) (h₃ : a + r = q + s) (h₄ : b + t = e + r) :
    parityPentagonTwoEvenIso C p hp W X Y Z a b c d e f q r s t h₃ h₄ =
      CentralWord.twoRoute W X Y Z
        (parityPairCompare C p hp a r q s h₃) (parityPairCompare C p hp b t e r h₄) := by
  unfold parityPentagonTwoEvenIso CentralWord.twoRoute
  simp only [scalarFreeAssociatorEvenIso_eq_central C p hp]
  rfl

theorem parity_wordThree_eq (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₅ : d + t = f + s) :
    CentralWord.wordThree (parityPairCompare C p hp a b c d h₁)
      (parityPairCompare C p hp c f e q h₂) (parityPairCompare C p hp d t f s h₅) =
      MonoidalWord.threeMoves (parityCenterFunctor C p hp)
        (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (.ofAdd e) (.ofAdd f)
        (.ofAdd q) (.ofAdd r) (.ofAdd s) (.ofAdd t)
        (congrArg Multiplicative.ofAdd h₁) (congrArg Multiplicative.ofAdd h₂)
        (congrArg Multiplicative.ofAdd h₅) := by
  apply Iso.ext
  simp only [CentralWord.wordThree, MonoidalWord.threeMoves, MonoidalWord.replaceLeft,
    MonoidalWord.replaceRight, Iso.trans_hom, Category.assoc]
  rfl

theorem parity_wordTwo_eq (a b c d e f q r s t : ZMod 2)
    (h₃ : a + r = q + s) (h₄ : b + t = e + r) :
    CentralWord.wordTwo (parityPairCompare C p hp a r q s h₃)
      (parityPairCompare C p hp b t e r h₄) =
      MonoidalWord.twoBraidedMoves (parityCenterFunctor C p hp)
        (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (.ofAdd e) (.ofAdd f)
        (.ofAdd q) (.ofAdd r) (.ofAdd s) (.ofAdd t)
        (congrArg Multiplicative.ofAdd h₃) (congrArg Multiplicative.ofAdd h₄) := by
  apply Iso.ext
  simp only [CentralWord.wordTwo, MonoidalWord.twoBraidedMoves, MonoidalWord.replaceRight,
    Iso.trans_hom, Category.assoc]
  rfl

end RMod.Classification
