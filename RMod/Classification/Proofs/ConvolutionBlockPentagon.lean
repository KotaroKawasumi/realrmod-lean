import RMod.Classification.Proofs.ConvolutionPentagonExpansion
import RMod.Classification.Proofs.WeightedPentagon

/-!
# Equality of the two actual fourfold block routes

The only difference between the source types is the parenthesization of
the total prefix degree. After its explicit equality transport, all five
blocks are the weighted local pentagon on the four original component
objects. The fermionic parameter equation supplies exactly its scalar
condition.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory MonoidalCategory

attribute [local implicit_reducible] convolutionFourLeftFamily convolutionFourInnerFamily
  convolutionFourMiddleFamily convolutionFourOuterFamily convolutionFourRightFamily
  convolutionLeftFamily convolutionRightFamily convolutionEvenFamily twistSummand convolutionSummandObj

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (ht : TwistLaws t)

theorem convolutionBlockPentagon_heq (W X Y Z : PullbackObj C t) (k g h l : t.group) :
    HEq (convolutionBlockPentagonThree C hC t ht W X Y Z k g h l).hom.hom
      (convolutionBlockPentagonTwo C hC t ht W X Y Z k g h l).hom.hom := by
  dsimp only [convolutionBlockPentagonThree, convolutionBlockPentagonTwo,
    convolutionBlockPentagonThreeOfParity, convolutionBlockPentagonTwoOfParity, convolutionBlockIsoOfParity]
  generalize_proofs hC₀ hm hm' o₁ i₁ p₁ e₁ o₅ i₅ p₅ e₅ o₂ i₂ p₂ e₂ o₄ i₄ p₄ e₄ o₃ i₃ p₃ e₃
  revert o₁ i₁ p₁ e₁ o₅ i₅ p₅ e₅ o₂ i₂ p₂ e₂ o₄ i₄ p₄ e₄ o₃ i₃ p₃ e₃
  dsimp only [convolutionFourLeftFamily, convolutionFourRightFamily, convolutionLeftFamily,
    convolutionRightFamily, convolutionEvenFamily, convolutionSummandObj, twistSummand]
  generalize he : (g * h) * l = q
  have he' : q = g * (h * l) := by simpa only [mul_assoc] using he.symm
  clear he
  subst q
  generalize he : (g * h)⁻¹ * (g * (h * l)) = q
  have he' : q = l := by simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using he.symm
  clear he
  subst q
  generalize he : (g * (h * l))⁻¹ * k = q
  have he' : q = l⁻¹ * (h⁻¹ * (g⁻¹ * k)) := by simpa only [mul_inv_rev, mul_assoc] using he.symm
  clear he
  subst q
  generalize he : (h * l)⁻¹ * (g⁻¹ * k) = q
  have he' : q = l⁻¹ * (h⁻¹ * (g⁻¹ * k)) := by simpa only [mul_inv_rev, mul_assoc] using he.symm
  clear he
  subst q
  generalize he : (g * h)⁻¹ * k = q
  have he' : q = h⁻¹ * (g⁻¹ * k) := by simpa only [mul_inv_rev, mul_assoc] using he.symm
  clear he
  subst q
  generalize he : g⁻¹ * (g * (h * l)) = q
  have he' : q = h * l := by simpa only [inv_mul_cancel_left] using he.symm
  clear he
  subst q
  generalize he : g⁻¹ * (g * h) = q
  have he' : q = h := by simpa only [inv_mul_cancel_left] using he.symm
  clear he
  subst q
  generalize he : h⁻¹ * (h * l) = q
  have he' : q = l := by simpa only [inv_mul_cancel_left] using he.symm
  clear he
  subst q
  generalize he : (h * l) * (l⁻¹ * (h⁻¹ * (g⁻¹ * k))) = q
  have he' : q = g⁻¹ * k := by simpa only [mul_assoc, mul_inv_cancel_left] using he.symm
  clear he
  subst q
  generalize he : h * (h⁻¹ * (g⁻¹ * k)) = q
  have he' : q = g⁻¹ * k := by simpa only [mul_inv_cancel_left] using he.symm
  clear he
  subst q
  generalize he : l * (l⁻¹ * (h⁻¹ * (g⁻¹ * k))) = q
  have he' : q = h⁻¹ * (g⁻¹ * k) := by simpa only [mul_inv_cancel_left] using he.symm
  clear he
  subst q
  intro o₁ i₁ p₁ e₁ o₅ i₅ p₅ e₅ o₂ i₂ p₂ e₂ o₄ i₄ p₄ e₄ o₃ i₃ p₃ e₃
  let m := l⁻¹ * (h⁻¹ * (g⁻¹ * k))
  apply heq_of_eq
  exact localAssociator_pentagon
    (⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ : WeaklyPointedSuperfusion)
    C.pi hC.pi (W g).val (X h).val (Y l).val (Z m).val
    (t.nu g h) (t.nu (g * h) l) (t.nu h l) (t.nu g (h * l))
    (t.nu l m) (t.nu (h * l) m) (t.nu h (h⁻¹ * (g⁻¹ * k)))
    (t.nu (g * h) (h⁻¹ * (g⁻¹ * k))) (t.nu g (g⁻¹ * k)) (t.nu (g * (h * l)) m)
    p₁ p₂ p₃ p₄ p₅
    (t.omega g h l) (t.omega h l m) (t.omega g h (h⁻¹ * (g⁻¹ * k)))
    (t.omega (g * h) l m) (t.omega g (h * l) m)
    (by simpa only [m, mul_assoc, mul_inv_cancel_left] using ht.pentagon_scalar g h l m)

end RMod.Classification
