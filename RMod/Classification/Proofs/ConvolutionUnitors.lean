import RMod.Classification.Instances.ConvolutionUnitors

/-!
# Inverse and degree laws for the chosen unitors

The support reduction, the identification of the normalized parity
factor and the original unitors all have explicit even inverse maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)
  (t : TwistData) (ht : TwistLaws t) (X : PullbackObj C t) (k : t.group)

theorem convolutionLeftUnitor_evenIso :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (convolutionLeftUnitorData C hC t ht X k) :=
  evenIsoLaws_ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionLeftUnitorEvenIso C hC t ht X k)

theorem convolutionRightUnitor_evenIso :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (convolutionRightUnitorData C hC t ht X k) :=
  evenIsoLaws_ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionRightUnitorEvenIso C hC t ht X k)

end RMod.Classification
