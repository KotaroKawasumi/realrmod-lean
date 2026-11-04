import RMod.Classification.Instances.ConvolutionFourInsertions
import RMod.Classification.Instances.ConvolutionSummandFamilies
import RMod.Classification.Instances.ConvolutionAssociatorOfParity

/-!
The only parameter law used in this file is the parity cocycle.
No scalar normalization or pentagon for omega is assumed.

# Actual and blockwise convolution pentagon routes

The long route uses the right-associated prefix g*(h*l), whereas the
short route uses (g*h)*l. Keeping these source types explicit avoids
hiding the final group-associativity transport. Their targets are the
same fully right-associated fourfold summand.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory MonoidalCategory

attribute [local implicit_reducible] convolutionFourLeftFamily convolutionFourInnerFamily
  convolutionFourMiddleFamily convolutionFourOuterFamily convolutionFourRightFamily
  convolutionLeftFamily convolutionRightFamily convolutionEvenFamily twistSummand convolutionSummandObj

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))

noncomputable def convolutionBlockPentagonThreeOfParity (W X Y Z : PullbackObj C t) (k g h l : t.group) :
    convolutionFourLeftFamily C hC t W X Y Z k (g * (h * l)) (g * h) g ≅
      convolutionFourRightFamily C hC t W X Y Z k g h l :=
  let A₁ := tensorIso
    (tensorIso (convolutionBlockIsoOfParity C hC t hν W X Y (g * (h * l)) g h)
      (Iso.refl (referenceEvenObj C hC (Z ((g * (h * l))⁻¹ * k)).val)))
    (Iso.refl (referenceEvenObj C hC (C.pi.factor (t.nu (g * (h * l)) ((g * (h * l))⁻¹ * k)))))
  let A₂ := convolutionBlockIsoOfParity C hC t hν W (convolutionSummandObj C hC t X Y h) Z k g (h * l)
  let A₃ := tensorIso
    (tensorIso (Iso.refl (referenceEvenObj C hC (W g).val))
      (convolutionBlockIsoOfParity C hC t hν X Y Z (g⁻¹ * k) h l))
    (Iso.refl (referenceEvenObj C hC (C.pi.factor (t.nu g (g⁻¹ * k)))))
  (A₁ ≪≫ A₂) ≪≫ A₃

noncomputable def convolutionBlockPentagonTwoOfParity (W X Y Z : PullbackObj C t) (k g h l : t.group) :
    convolutionFourLeftFamily C hC t W X Y Z k ((g * h) * l) (g * h) g ≅
      convolutionFourRightFamily C hC t W X Y Z k g h l :=
  convolutionBlockIsoOfParity C hC t hν (convolutionSummandObj C hC t W X g) Y Z k (g * h) l ≪≫
    convolutionBlockIsoOfParity C hC t hν W X (convolutionSummandObj C hC t Y Z l) k g h

noncomputable def convolutionPentagonThreeOfParity (W X Y Z : PullbackObj C t) (k : t.group) :
    C.Hom
      (convolutionObj C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k).val
      (convolutionObj C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k).val :=
  C.comp (C.comp
    (convolutionHom C hC t (fun g => (convolutionAssociatorDataOfParity C hC t hν W X Y g).hom)
      (fun g => C.id (Z g).val) k)
    (convolutionAssociatorDataOfParity C hC t hν W (convolutionObj C hC t X Y) Z k).hom)
    (convolutionHom C hC t (fun g => C.id (W g).val)
      (fun g => (convolutionAssociatorDataOfParity C hC t hν X Y Z g).hom) k)

noncomputable def convolutionPentagonTwoOfParity (W X Y Z : PullbackObj C t) (k : t.group) :
    C.Hom
      (convolutionObj C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k).val
      (convolutionObj C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k).val :=
  C.comp (convolutionAssociatorDataOfParity C hC t hν (convolutionObj C hC t W X) Y Z k).hom
    (convolutionAssociatorDataOfParity C hC t hν W X (convolutionObj C hC t Y Z) k).hom

end RMod.Classification
