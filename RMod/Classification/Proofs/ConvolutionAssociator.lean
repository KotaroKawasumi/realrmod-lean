import RMod.Classification.Instances.ConvolutionAssociator

/-!
# The inverse and parity laws for the convolution associator

All constituent comparisons are actual even isomorphisms in Mathlib's
even category, so forgetting to the raw maps verifies their inverse and
degree laws without changing the data. Pentagon coherence is not used.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem convolutionAssociator_evenIso (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
    (X Y Z : PullbackObj C t) (k : t.group) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (convolutionAssociatorData C hC t ht X Y Z k) :=
  evenIsoLaws_ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionAssociatorEvenIso C hC t ht X Y Z k)

end RMod.Classification
