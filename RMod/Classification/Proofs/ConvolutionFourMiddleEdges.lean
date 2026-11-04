import RMod.Classification.Proofs.ConvolutionFourMiddleEdgesOfParity
import RMod.Classification.Proofs.ConvolutionFourFactorizations
import RMod.Classification.Proofs.ConvolutionNaturality

/-!
# The three remaining edges of the fourfold pentagon

Apply associator naturality to the inclusion of a fixed-degree summand
family. The threefold block equation and the exact fourfold
factorizations then identify each edge on the original chosen sums.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] convolutionFourLeftFamily convolutionFourInnerFamily
  convolutionFourMiddleFamily convolutionFourOuterFamily convolutionFourRightFamily
  convolutionLeftFamily convolutionRightFamily convolutionEvenFamily twistSummand convolutionSummandObj

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (ht : TwistLaws t)

theorem convolutionFourInnerInsertion_middle (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourInnerInsertion C hC t W X Y Z k (a * b) a c).hom
      (convolutionAssociatorData C hC t ht W (convolutionObj C hC t X Y) Z k).hom =
    C.comp (convolutionBlockIso C hC t ht W (convolutionSummandObj C hC t X Y c) Z k a b).hom.hom
      (convolutionFourOuterInsertion C hC t W X Y Z k a b c).hom :=
  convolutionFourInnerInsertion_middleOfParity C hC t ht.normalizer_parity W X Y Z k a b c

theorem convolutionFourLeftInsertion_short_first (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourLeftInsertion C hC t W X Y Z k (a * b) a c).hom
      (convolutionAssociatorData C hC t ht (convolutionObj C hC t W X) Y Z k).hom =
    C.comp (convolutionBlockIso C hC t ht (convolutionSummandObj C hC t W X c) Y Z k a b).hom.hom
      (convolutionFourMiddleInsertion C hC t W X Y Z k a c b).hom :=
  convolutionFourLeftInsertion_short_firstOfParity C hC t ht.normalizer_parity W X Y Z k a b c

theorem convolutionFourMiddleInsertion_short_last (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourMiddleInsertion C hC t W X Y Z k (a * b) a c).hom
      (convolutionAssociatorData C hC t ht W X (convolutionObj C hC t Y Z) k).hom =
    C.comp (convolutionBlockIso C hC t ht W X (convolutionSummandObj C hC t Y Z c) k a b).hom.hom
      (convolutionFourRightInsertion C hC t W X Y Z k a b c).hom :=
  convolutionFourMiddleInsertion_short_lastOfParity C hC t ht.normalizer_parity W X Y Z k a b c

end RMod.Classification
