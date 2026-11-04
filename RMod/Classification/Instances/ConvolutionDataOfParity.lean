import RMod.Classification.Instances.ConvolutionAssociatorOfParity
import RMod.Classification.Instances.ConvolutionUnitorsOfParity

/-!
# The complete construction data before scalar coherence is known

Normalized parity and its cocycle already form every raw operation of
the convolution category, including its specified parity structure.
Scalar normalization and the pentagon are laws still to be proved for
these data. This interface keeps the separation explicit when
transporting coherence along the constructed reconstruction equivalence.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
  (hνL : ∀ g : t.group, t.nu 1 g = 0) (hνR : ∀ g : t.group, t.nu g 1 = 0)

noncomputable def convolutionTensorDataOfParity : PullbackTensorData C t where
  tensorObj := convolutionObj C hC t
  tensorHom := convolutionHom C hC t
  tensorUnit := pullbackUnitObj C hC t
  associatorHom X Y Z k := (convolutionAssociatorDataOfParity C hC t hν X Y Z k).hom
  associatorInv X Y Z k := (convolutionAssociatorDataOfParity C hC t hν X Y Z k).inv
  leftUnitorHom X k := (convolutionLeftUnitorDataOfParity C hC t hνL X k).hom
  leftUnitorInv X k := (convolutionLeftUnitorDataOfParity C hC t hνL X k).inv
  rightUnitorHom X k := (convolutionRightUnitorDataOfParity C hC t hνR X k).hom
  rightUnitorInv X k := (convolutionRightUnitorDataOfParity C hC t hνR X k).inv
  piObj := pullbackPiObj C hC t
  piHom := pullbackPiHom C hC t
  piInv := pullbackPiInv C hC t

noncomputable def convolutionDataOfParity : PiSuperfusionData.{0, 0} :=
  (convolutionTensorDataOfParity C hC t hν hνL hνR).toPiSuperfusionData C t

end RMod.Classification
