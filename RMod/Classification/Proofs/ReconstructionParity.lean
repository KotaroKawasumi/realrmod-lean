import RMod.Classification.Instances.ReconstructionTwistData
import RMod.Classification.Proofs.ReconstructionNuCocycle

/-!
# The parity equality needed to construct reconstruction's associator

This is already a theorem of the actual binary comparisons. It can be
used before any scalar coherence for the extracted omega is established.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem reconstruction_normalizer_parity (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionTwistData A C hC).nu g h + (reconstructionTwistData A C hC).nu (g * h) k =
      (reconstructionTwistData A C hC).nu h k + (reconstructionTwistData A C hC).nu g (h * k) :=
  componentTripleParity (reconstructionComponentSystem A C hC)
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion) (reconstruction_target_product A C hC)
    (reconstructionNu A C hC) (normalizedReconstructionComparison A C hC) g h k

end RMod.Classification
