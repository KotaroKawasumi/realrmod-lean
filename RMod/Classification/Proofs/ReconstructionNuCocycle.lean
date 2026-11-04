import RMod.Classification.Proofs.NormalizedReconstructionComparison
import RMod.Classification.Proofs.ComponentCocycle

/-!
# The extracted reconstruction degree is a two-cocycle

Apply the actual triple comparison argument to the selected component
equivalences and the already normalized binary maps. The only inputs
are the proved orbit products and the completed category structures.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem reconstructionNu_cocycle (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
    (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    reconstructionNu A C hC h k + reconstructionNu A C hC (g * h) k +
      reconstructionNu A C hC g (h * k) + reconstructionNu A C hC g h = 0 :=
  componentNu_cocycle (reconstructionComponentSystem A C hC)
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion) (reconstruction_target_product A C hC)
    (reconstructionNu A C hC) (normalizedReconstructionComparison A C hC) g h k

end RMod.Classification
