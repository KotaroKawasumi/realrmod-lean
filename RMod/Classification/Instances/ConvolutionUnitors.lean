import RMod.Classification.Instances.ConvolutionUnitorsOfParity

/-! # The actual convolution unitors for a lawful twist

Use the specified parity-normalized unitors. Their data do not require
any scalar normalization or pentagon assumption.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionLeftUnitBlock (ht : TwistLaws t) (X : PullbackObj C t) (k : t.group) :
    convolutionEvenFamily C hC t (pullbackUnitObj C hC t) X k 1 ≅ referenceEvenObj C hC (X k).val :=
  convolutionLeftUnitBlockOfParity C hC t ht.nu_one_left X k

noncomputable def convolutionRightUnitBlock (ht : TwistLaws t) (X : PullbackObj C t) (k : t.group) :
    convolutionEvenFamily C hC t X (pullbackUnitObj C hC t) k k ≅ referenceEvenObj C hC (X k).val :=
  convolutionRightUnitBlockOfParity C hC t ht.nu_one_right X k

noncomputable def convolutionLeftUnitorEvenIso (ht : TwistLaws t) (X : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t (pullbackUnitObj C hC t) X k).val ≅
      referenceEvenObj C hC (X k).val :=
  convolutionLeftUnitorEvenIsoOfParity C hC t ht.nu_one_left X k

noncomputable def convolutionRightUnitorEvenIso (ht : TwistLaws t) (X : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t X (pullbackUnitObj C hC t) k).val ≅
      referenceEvenObj C hC (X k).val :=
  convolutionRightUnitorEvenIsoOfParity C hC t ht.nu_one_right X k

noncomputable def convolutionLeftUnitorData (ht : TwistLaws t) (X : PullbackObj C t) (k : t.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC t (pullbackUnitObj C hC t) X k).val (X k).val :=
  convolutionLeftUnitorDataOfParity C hC t ht.nu_one_left X k

noncomputable def convolutionRightUnitorData (ht : TwistLaws t) (X : PullbackObj C t) (k : t.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC t X (pullbackUnitObj C hC t) k).val (X k).val :=
  convolutionRightUnitorDataOfParity C hC t ht.nu_one_right X k

end RMod.Classification
