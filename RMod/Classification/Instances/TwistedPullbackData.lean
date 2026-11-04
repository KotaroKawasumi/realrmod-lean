import RMod.Classification.Instances.ConvolutionAssociator
import RMod.Classification.Instances.ConvolutionUnitors

/-!
# Construction data for the abstract twisted pullback

The underlying group-indexed objects and Hom operations are fixed by the
pullback interface. The tensor is the actual chosen convolution; its
associator is the blockwise omega times R-inverse L map, and its unitors
are the normalized supported-unit comparisons. Every operation uses C's
own structure. Category, coherence, fusion and duality laws are proved
separately for precisely these data.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def convolutionTensorData (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t) : PullbackTensorData C t where
  tensorObj := convolutionObj C hC t
  tensorHom := convolutionHom C hC t
  tensorUnit := pullbackUnitObj C hC t
  associatorHom X Y Z k := (convolutionAssociatorData C hC t ht X Y Z k).hom
  associatorInv X Y Z k := (convolutionAssociatorData C hC t ht X Y Z k).inv
  leftUnitorHom X k := (convolutionLeftUnitorData C hC t ht X k).hom
  leftUnitorInv X k := (convolutionLeftUnitorData C hC t ht X k).inv
  rightUnitorHom X k := (convolutionRightUnitorData C hC t ht X k).hom
  rightUnitorInv X k := (convolutionRightUnitorData C hC t ht X k).inv
  piObj := pullbackPiObj C hC t
  piHom := pullbackPiHom C hC t
  piInv := pullbackPiInv C hC t

/-- The advertised definition hole is filled by the construction from C.
No concrete real reference model is used by this definition. -/
noncomputable def twistedPullbackData (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t) : PiSuperfusionData.{0, 0} :=
  (convolutionTensorData C hC t ht).toPiSuperfusionData C t

end RMod.Classification
