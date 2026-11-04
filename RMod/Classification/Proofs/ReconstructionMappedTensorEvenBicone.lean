import RMod.Classification.Instances.ReconstructionMappedTensorEvenBicone
import RMod.Classification.Proofs.BiconeToEven

/-! # Universality of the actual mapped presentation among even maps -/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def reconstructionMappedTensorEvenBicone_isBilimit (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
    (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionMappedTensorEvenBicone A C hC X Y k).IsBilimit := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact biconeToEven_isBilimit _ _ _ _ (reconstructionMappedTensorBicone_isBilimit A C hC X Y k)

end RMod.Classification
