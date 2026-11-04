import RMod.Classification.Instances.NormalizedReconstructionComparison
import RMod.Classification.Proofs.ComponentSystemUnitCoherence

/-!
# Both unit restrictions of the normalized binary choices

The left-unit clause holds by construction. The right-unit clause also
holds when both group arguments are one, because the specified component
unit comparisons agree exactly, including their inverse maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem normalizedReconstructionComparison_one_left (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    normalizedReconstructionComparisonData A C hC 1 g =
      ((reconstructionComponentSystem A C hC).leftUnitComparison g
        (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion 1 g)
        (reconstruction_target_product A C hC 1 g)).data := by
  classical
  simp [normalizedReconstructionComparisonData]

theorem normalizedReconstructionComparison_one_right (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    normalizedReconstructionComparisonData A C hC g 1 =
      ((reconstructionComponentSystem A C hC).rightUnitComparison g
        (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g 1)
        (reconstruction_target_product A C hC g 1)).data := by
  classical
  by_cases hg : g = 1
  · subst g
    rw [normalizedReconstructionComparison_one_left]
    exact congrArg TensorComparison.data ((reconstructionComponentSystem A C hC).unitComparisons_equal
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion 1 1)
      (reconstruction_target_product A C hC 1 1))
  · simp [normalizedReconstructionComparisonData, hg]

end RMod.Classification
