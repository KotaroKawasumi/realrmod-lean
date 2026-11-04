import RMod.Classification.Instances.ReconstructionMappedTensorBicone
import RMod.Classification.Proofs.ReconstructionTensorComponentBicone

/-!
# The component realization preserves the even tensor presentation

Mathlib's preservation theorem for additive functors transports the
finite bilimit. The separate component superfunctor laws preserve the
evenness of each inclusion and projection.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y : LinearCategory A.toWeaklyPointedSuperfusion) (k : SimpleOrbit A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionMappedTensorBicone_isBilimit :
    (reconstructionMappedTensorBicone A C hC X Y k).IsBilimit :=
  isBilimitOfPreserves _ (reconstructionTensorComponentBicone_isBilimit A X Y k)

theorem reconstructionMappedTensorBicone_inclusion_even (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.IsHomogeneous 0 ((reconstructionMappedTensorBicone A C hC X Y k).ι g) :=
  ((reconstructionComponentSystem A C hC).component k).laws.forward.map_grade _
    (reconstructionTensorComponentBicone_inclusion_even A X Y k g)

theorem reconstructionMappedTensorBicone_projection_even (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.IsHomogeneous 0 ((reconstructionMappedTensorBicone A C hC X Y k).π g) :=
  ((reconstructionComponentSystem A C hC).component k).laws.forward.map_grade _
    (reconstructionTensorComponentBicone_projection_even A X Y k g)

end RMod.Classification
