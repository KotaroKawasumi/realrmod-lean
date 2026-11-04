import RMod.Classification.Instances.ComponentOmega
import RMod.Classification.Instances.NormalizedReconstructionComparison

/-!
# Actual tensorators and associator scalars for reconstruction

Use the normalized binary comparisons already chosen from the complete
source category and the abstract reference property. The resulting
scalar uses only those component functors and the reference's specified
parity structure; no concrete universal-category data enter here.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def reconstructionTensorComparison (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :=
  parityTensorComparison (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (normalizedReconstructionComparison A C hC g h)

noncomputable def reconstructionNormalizedLeft (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion) :=
  componentNormalizedLeft (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (reconstructionComponentSystem A C hC)
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion) (reconstruction_target_product A C hC)
    (reconstructionNu A C hC) (normalizedReconstructionComparison A C hC) g h k

noncomputable def reconstructionNormalizedRight (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion) :=
  componentParityTripleRight (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (reconstructionComponentSystem A C hC)
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion) (reconstruction_target_product A C hC)
    (reconstructionNu A C hC) (normalizedReconstructionComparison A C hC) g h k

noncomputable def reconstructionOmega (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion) : ℝˣ :=
  componentOmega (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (reconstructionComponentSystem A C hC)
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion) (reconstruction_target_product A C hC)
    (reconstructionNu A C hC) (normalizedReconstructionComparison A C hC) g h k

end RMod.Classification
