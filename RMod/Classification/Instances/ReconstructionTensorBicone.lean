import RMod.Classification.Instances.TensorBicone
import RMod.Classification.Proofs.ReconstructionSourceBicone

/-! # The pair-indexed tensor presentation of arbitrary source objects -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

noncomputable def reconstructionTensorBicone (A : PiSuperfusion.{0, 0})
    (X Y : LinearCategory A.toWeaklyPointedSuperfusion) :=
  tensorBicone A.toWeaklyPointedSuperfusion (reconstructionSourceBicone A X) (reconstructionSourceBicone A Y)
    (reconstructionSourceBicone_inclusion_even A X)

end RMod.Classification
