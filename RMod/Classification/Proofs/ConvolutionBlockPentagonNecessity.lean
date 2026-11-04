import RMod.Classification.Instances.ConvolutionPentagonRoutesOfParity
import RMod.Classification.Proofs.WeightedPentagonNecessity
import RMod.Classification.Proofs.ParityPentagonNonvanishing
import Batteries.Tactic.GeneralizeProofs

/-!
# Actual fourfold block equality forces the fermionic scalar equation

Normalize the explicit group-index transports in both retained block
paths. The resulting maps are the weighted local parity pentagon. Its
source is nonzero when the four component objects are nonzero, so the
proved scalar cancellation theorem recovers the parameter equation.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory MonoidalCategory

attribute [local implicit_reducible] convolutionFourLeftFamily convolutionFourInnerFamily
  convolutionFourMiddleFamily convolutionFourOuterFamily convolutionFourRightFamily
  convolutionLeftFamily convolutionRightFamily convolutionEvenFamily twistSummand convolutionSummandObj


variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))

theorem convolutionBlockPentagon_scalar_of_heq (W X Y Z : PullbackObj C t) (k g h l : t.group)
    (hW : C.id (W g).val ≠ C.zero) (hX : C.id (X h).val ≠ C.zero)
    (hY : C.id (Y l).val ≠ C.zero) (hZ : C.id (Z (l⁻¹ * (h⁻¹ * (g⁻¹ * k)))).val ≠ C.zero)
    (he : HEq (convolutionBlockPentagonThreeOfParity C hC t hν W X Y Z k g h l).hom.hom
      (convolutionBlockPentagonTwoOfParity C hC t hν W X Y Z k g h l).hom.hom) :
    let m := l⁻¹ * (h⁻¹ * (g⁻¹ * k))
    t.omega h l m * t.omega g (h * l) m * t.omega g h l =
      realSign (t.nu g h * t.nu l m) * (t.omega (g * h) l m * t.omega g h (l * m)) := by
  dsimp only
  revert he
  dsimp only [convolutionBlockPentagonThreeOfParity, convolutionBlockPentagonTwoOfParity, convolutionBlockIsoOfParity]
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
  intro o₁ i₁ p₁ e₁ o₅ i₅ p₅ e₅ o₂ i₂ p₂ e₂ o₄ i₄ p₄ e₄ o₃ i₃ p₃ e₃ he
  let m := l⁻¹ * (h⁻¹ * (g⁻¹ * k))
  have hp := localAssociator_pentagon_unit_scalar_of_eq
    (⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ : WeaklyPointedSuperfusion)
    C.pi hC.pi (W g).val (X h).val (Y l).val (Z m).val
    (t.nu g h) (t.nu (g * h) l) (t.nu h l) (t.nu g (h * l))
    (t.nu l m) (t.nu (h * l) m) (t.nu h (h⁻¹ * (g⁻¹ * k)))
    (t.nu (g * h) (h⁻¹ * (g⁻¹ * k))) (t.nu g (g⁻¹ * k)) (t.nu (g * (h * l)) m)
    p₁ p₂ p₃ p₄ p₅
    (t.omega g h l) (t.omega h l m) (t.omega g h (h⁻¹ * (g⁻¹ * k)))
    (t.omega (g * h) l m) (t.omega g (h * l) m)
    (parityPentagon_source_id_ne_zero
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ C.pi hC.pi
      (W g).val (X h).val (Y l).val (Z m).val _ _ _ hW hX hY hZ)
    (eq_of_heq he)
  simpa only [m, mul_inv_cancel_left] using hp

end RMod.Classification
