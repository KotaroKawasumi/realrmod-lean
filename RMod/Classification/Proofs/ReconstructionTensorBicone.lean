import RMod.Classification.Instances.ReconstructionTensorBicone
import RMod.Classification.Proofs.TensorBicone

/-! # Universality and evenness of the tensor presentation -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A : PiSuperfusion.{0, 0}) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionTensorBicone_isBilimit : (reconstructionTensorBicone A X Y).IsBilimit := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact tensorBicone_isBilimit _ _ _ (reconstructionSourceBicone_inclusion_even A X)
    (reconstructionSourceBicone_projection_even A X)
    (reconstructionSourceBicone_isBilimit A X) (reconstructionSourceBicone_isBilimit A Y)

theorem reconstructionTensorBicone_inclusion_even (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionTensorBicone A X Y).ι (g, h)) :=
  tensor_even A.laws.toWeaklyPointedSuperfusionLaws (reconstructionSourceBicone_inclusion_even A X g)
    (reconstructionSourceBicone_inclusion_even A Y h)

theorem reconstructionTensorBicone_projection_even (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionTensorBicone A X Y).π (g, h)) :=
  tensor_even A.laws.toWeaklyPointedSuperfusionLaws (reconstructionSourceBicone_projection_even A X g)
    (reconstructionSourceBicone_projection_even A Y h)

end RMod.Classification
