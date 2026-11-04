import RMod.Classification.Instances.ConvolutionAssociatorOfParity

/-! # The convolution associator for a lawful twist

The actual maps use the parity-only construction. Scalar coherence is
proved separately; it is not needed to select the maps or their inverses.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionBlockIso (ht : TwistLaws t) (X Y Z : PullbackObj C t)
    (k g h : t.group) :
    convolutionLeftFamily C hC t X Y Z k (g * h) g ≅ convolutionRightFamily C hC t X Y Z k g h :=
  convolutionBlockIsoOfParity C hC t ht.normalizer_parity X Y Z k g h

noncomputable def convolutionBlocksIso (ht : TwistLaws t) (X Y Z : PullbackObj C t) (k : t.group) :
    (⨁ fun i : (_ : t.group) × t.group => convolutionLeftFamily C hC t X Y Z k i.1 i.2) ≅
      ⨁ fun i : (_ : t.group) × t.group => convolutionRightFamily C hC t X Y Z k i.1 i.2 :=
  convolutionBlocksIsoOfParity C hC t ht.normalizer_parity X Y Z k

noncomputable def convolutionAssociatorEvenIso (ht : TwistLaws t)
    (X Y Z : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t (convolutionObj C hC t X Y) Z k).val ≅
      referenceEvenObj C hC (convolutionObj C hC t X (convolutionObj C hC t Y Z) k).val :=
  convolutionAssociatorEvenIsoOfParity C hC t ht.normalizer_parity X Y Z k

noncomputable def convolutionAssociatorData (ht : TwistLaws t)
    (X Y Z : PullbackObj C t) (k : t.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC t (convolutionObj C hC t X Y) Z k).val
      (convolutionObj C hC t X (convolutionObj C hC t Y Z) k).val :=
  convolutionAssociatorDataOfParity C hC t ht.normalizer_parity X Y Z k

end RMod.Classification
