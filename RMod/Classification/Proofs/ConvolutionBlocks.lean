import RMod.Classification.Instances.ConvolutionAssociator
import RMod.Classification.Proofs.ConvolutionBlocksOfParity

/-!
# The actual associator on an individual threefold summand

The reindexing of the middle biproduct takes `(g*h,g)` to `(g,h)`.
Its block is precisely the selected local associator. Cancelling the
expansion comparisons then gives the corresponding equation on the
original convolution objects.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] convolutionEvenFamily convolutionLeftFamily
  convolutionRightFamily twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (ht : TwistLaws t)

theorem convolutionBlocksIso_inclusion (X Y Z : PullbackObj C t) (k g h : t.group) :
    biproduct.ι (fun i : (_ : t.group) × t.group => convolutionLeftFamily C hC t X Y Z k i.1 i.2)
        ⟨g * h, g⟩ ≫ (convolutionBlocksIso C hC t ht X Y Z k).hom =
      (convolutionBlockIso C hC t ht X Y Z k g h).hom ≫
        biproduct.ι (fun i : (_ : t.group) × t.group => convolutionRightFamily C hC t X Y Z k i.1 i.2)
          ⟨g, h⟩ :=
  convolutionBlocksIsoOfParity_inclusion C hC t ht.normalizer_parity X Y Z k g h

theorem convolutionAssociator_inclusion (X Y Z : PullbackObj C t) (k g h : t.group) :
    convolutionLeftInsertionEven C hC t X Y Z k (g * h) g ≫
      (convolutionAssociatorEvenIso C hC t ht X Y Z k).hom =
        (convolutionBlockIso C hC t ht X Y Z k g h).hom ≫
          convolutionRightInsertionEven C hC t X Y Z k g h :=
  convolutionAssociator_inclusionOfParity C hC t ht.normalizer_parity X Y Z k g h

end RMod.Classification
