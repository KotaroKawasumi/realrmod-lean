import RMod.Classification.Instances.ConvolutionPentagonRoutesOfParity
import RMod.Classification.Instances.ConvolutionFourInsertions
import RMod.Classification.Instances.ConvolutionSummandFamilies
import RMod.Classification.Instances.ConvolutionAssociator

/-!
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
  (ht : TwistLaws t)

noncomputable def convolutionBlockPentagonThree (W X Y Z : PullbackObj C t) (k g h l : t.group) :
    convolutionFourLeftFamily C hC t W X Y Z k (g * (h * l)) (g * h) g ≅
      convolutionFourRightFamily C hC t W X Y Z k g h l :=
  convolutionBlockPentagonThreeOfParity C hC t ht.normalizer_parity W X Y Z k g h l

noncomputable def convolutionBlockPentagonTwo (W X Y Z : PullbackObj C t) (k g h l : t.group) :
    convolutionFourLeftFamily C hC t W X Y Z k ((g * h) * l) (g * h) g ≅
      convolutionFourRightFamily C hC t W X Y Z k g h l :=
  convolutionBlockPentagonTwoOfParity C hC t ht.normalizer_parity W X Y Z k g h l

noncomputable def convolutionPentagonThree (W X Y Z : PullbackObj C t) (k : t.group) :
    C.Hom
      (convolutionObj C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k).val
      (convolutionObj C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k).val :=
  convolutionPentagonThreeOfParity C hC t ht.normalizer_parity W X Y Z k

noncomputable def convolutionPentagonTwo (W X Y Z : PullbackObj C t) (k : t.group) :
    C.Hom
      (convolutionObj C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k).val
      (convolutionObj C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k).val :=
  convolutionPentagonTwoOfParity C hC t ht.normalizer_parity W X Y Z k

end RMod.Classification
