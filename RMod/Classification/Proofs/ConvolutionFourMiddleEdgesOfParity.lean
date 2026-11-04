import RMod.Classification.Proofs.ConvolutionFourFactorizations
import RMod.Classification.Proofs.ConvolutionNaturality

/-!
The only parameter law used in this file is the parity cocycle.
No scalar normalization or pentagon for omega is assumed.

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
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))

theorem convolutionFourInnerInsertion_middleOfParity (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourInnerInsertion C hC t W X Y Z k (a * b) a c).hom
      (convolutionAssociatorDataOfParity C hC t hν W (convolutionObj C hC t X Y) Z k).hom =
    C.comp (convolutionBlockIsoOfParity C hC t hν W (convolutionSummandObj C hC t X Y c) Z k a b).hom.hom
      (convolutionFourOuterInsertion C hC t W X Y Z k a b c).hom := by
  erw [← convolutionFourInner_factor C hC t W X Y Z k (a * b) a c,
    hC.comp_assoc, convolutionAssociatorOfParity_naturality, ← hC.comp_assoc,
    convolutionAssociatorOfParity_inclusion_hom, hC.comp_assoc, convolutionFourOuter_factor]

theorem convolutionFourLeftInsertion_short_firstOfParity (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourLeftInsertion C hC t W X Y Z k (a * b) a c).hom
      (convolutionAssociatorDataOfParity C hC t hν (convolutionObj C hC t W X) Y Z k).hom =
    C.comp (convolutionBlockIsoOfParity C hC t hν (convolutionSummandObj C hC t W X c) Y Z k a b).hom.hom
      (convolutionFourMiddleInsertion C hC t W X Y Z k a c b).hom := by
  erw [← convolutionFourLeft_factor C hC t W X Y Z k (a * b) a c,
    hC.comp_assoc, convolutionAssociatorOfParity_naturality, ← hC.comp_assoc,
    convolutionAssociatorOfParity_inclusion_hom, hC.comp_assoc, convolutionFourMiddle_factor_first]

theorem convolutionFourMiddleInsertion_short_lastOfParity (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourMiddleInsertion C hC t W X Y Z k (a * b) a c).hom
      (convolutionAssociatorDataOfParity C hC t hν W X (convolutionObj C hC t Y Z) k).hom =
    C.comp (convolutionBlockIsoOfParity C hC t hν W X (convolutionSummandObj C hC t Y Z c) k a b).hom.hom
      (convolutionFourRightInsertion C hC t W X Y Z k a b c).hom := by
  erw [← convolutionFourMiddle_factor_last C hC t W X Y Z k (a * b) a c,
    hC.comp_assoc, convolutionAssociatorOfParity_naturality, ← hC.comp_assoc,
    convolutionAssociatorOfParity_inclusion_hom, hC.comp_assoc, convolutionFourRight_factor]

end RMod.Classification
