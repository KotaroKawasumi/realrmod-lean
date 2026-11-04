import RMod.Classification.Instances.ReconstructionTripleComponents
import RMod.Classification.Proofs.ReconstructionComponentProjection

/-!
# The selected product-component inclusion retains the original tensor map

The tensor of the two input component objects belongs to the intrinsic
product span. Its incoming tensor inclusion therefore sees the selected
component projector as the identity.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : PiSuperfusion.{0, 0}) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTensorSpanInclusion_inclusion :
    A.data.comp (reconstructionTensorSpanInclusion A X Y g h).hom
      ((reconstructionSourceBicone A (A.data.tensorObj X Y)).ι (g * h)) =
      (reconstructionTensorBicone A X Y).ι (g, h) := by
  let f := (reconstructionTensorBicone A X Y).ι (g, h)
  have hp := reconstructionComponentProjection_incoming A (g * h)
    (reconstructionTensorSpanObject A X Y g h).property f
  exact (A.laws.comp_assoc _ _ _).trans hp

theorem reconstructionTensorSpanInclusion_even :
    A.data.IsHomogeneous 0 (reconstructionTensorSpanInclusion A X Y g h).hom :=
  comp_even A.laws.toWeaklyPointedSuperfusionLaws
    (tensor_even A.laws.toWeaklyPointedSuperfusionLaws
      (reconstructionSourceBicone_inclusion_even A X g)
      (reconstructionSourceBicone_inclusion_even A Y h))
    (reconstructionSourceBicone_projection_even A (A.data.tensorObj X Y) (g * h))

end RMod.Classification
