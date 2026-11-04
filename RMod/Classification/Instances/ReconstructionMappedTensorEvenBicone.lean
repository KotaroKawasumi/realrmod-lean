import RMod.Classification.Proofs.ReconstructionMappedTensorBicone
import RMod.Classification.Instances.BiconeToEven

/-! # The mapped tensor presentation in the reference even category -/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def reconstructionMappedTensorEvenBicone (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
    (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :=
  biconeToEven C.toWeaklyPointedSuperfusion (reconstructionMappedTensorBicone A C hC X Y k)
    (reconstructionMappedTensorBicone_projection_even A C hC X Y k)
    (reconstructionMappedTensorBicone_inclusion_even A C hC X Y k)

end RMod.Classification
