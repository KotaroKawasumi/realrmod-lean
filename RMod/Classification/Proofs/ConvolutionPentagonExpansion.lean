import RMod.Classification.Proofs.ConvolutionPentagonExpansionOfParity
import RMod.Classification.Instances.ConvolutionPentagonRoutes
import RMod.Classification.Proofs.ConvolutionFourWhiskerEdges
import RMod.Classification.Proofs.ConvolutionFourMiddleEdges
import Mathlib.CategoryTheory.CommSq

/-!
# Both convolution pentagon paths on a fourfold summand

Compose the five checked insertion squares using Mathlib's horizontal
composition of commutative squares. The resulting block paths retain
all five actual scalar-weighted associators.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (ht : TwistLaws t)

theorem convolutionPentagonThree_inclusion (W X Y Z : PullbackObj C t) (k g h l : t.group) :
    C.comp (convolutionFourLeftInsertion C hC t W X Y Z k (g * (h * l)) (g * h) g).hom
      (convolutionPentagonThree C hC t ht W X Y Z k) =
    C.comp (convolutionBlockPentagonThree C hC t ht W X Y Z k g h l).hom.hom
      (convolutionFourRightInsertion C hC t W X Y Z k g h l).hom :=
  convolutionPentagonThreeOfParity_inclusion C hC t ht.normalizer_parity W X Y Z k g h l

theorem convolutionPentagonTwo_inclusion (W X Y Z : PullbackObj C t) (k g h l : t.group) :
    C.comp (convolutionFourLeftInsertion C hC t W X Y Z k ((g * h) * l) (g * h) g).hom
      (convolutionPentagonTwo C hC t ht W X Y Z k) =
    C.comp (convolutionBlockPentagonTwo C hC t ht W X Y Z k g h l).hom.hom
      (convolutionFourRightInsertion C hC t W X Y Z k g h l).hom :=
  convolutionPentagonTwoOfParity_inclusion C hC t ht.normalizer_parity W X Y Z k g h l

end RMod.Classification
