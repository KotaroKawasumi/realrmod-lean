import RMod.Classification.Instances.ComponentSystemUnit
import RMod.Classification.Proofs.ReconstructionNuUnit

/-!
# Binary comparison choices normalized at the unit

At the left unit use the specified left unitor extension. At the right
unit use the right extension; elsewhere keep the previously selected
comparison. The data select maps first. The already proved vanishing
of the unit degrees then gives laws at the extracted degree, and the
completed comparison contains precisely these data and laws.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def normalizedReconstructionComparisonData
    (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    TensorComparisonData
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g)
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion h)
      (referenceSimpleRepresentative C hC (simpleOrbitType A g))
      (referenceSimpleRepresentative C hC (simpleOrbitType A h))
      ((reconstructionComponentSystem A C hC).component g).forwardFunctor.data
      ((reconstructionComponentSystem A C hC).component h).forwardFunctor.data
      (reconstructionProductEquivalence A C hC g h).forwardFunctor.data := by
  classical
  by_cases hg : g = 1
  · subst g
    exact ((reconstructionComponentSystem A C hC).leftUnitComparison h
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion 1 h)
      (reconstruction_target_product A C hC 1 h)).data
  · by_cases hh : h = 1
    · subst h
      exact ((reconstructionComponentSystem A C hC).rightUnitComparison g
        (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g 1)
        (reconstruction_target_product A C hC g 1)).data
    · exact (reconstructionBinaryComparison A C hC g h).data

theorem normalizedReconstructionComparisonLaws (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    TensorComparisonLaws
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g)
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion h)
      (referenceSimpleRepresentative C hC (simpleOrbitType A g))
      (referenceSimpleRepresentative C hC (simpleOrbitType A h))
      (reconstructionNu A C hC g h) (normalizedReconstructionComparisonData A C hC g h) := by
  classical
  by_cases hg : g = 1
  · subst g
    simp only [normalizedReconstructionComparisonData, reconstructionNu_one_left]
    exact ((reconstructionComponentSystem A C hC).leftUnitComparison h
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion 1 h)
      (reconstruction_target_product A C hC 1 h)).laws
  · by_cases hh : h = 1
    · subst h
      simp only [normalizedReconstructionComparisonData, dif_neg hg, reconstructionNu_one_right]
      exact ((reconstructionComponentSystem A C hC).rightUnitComparison g
        (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g 1)
        (reconstruction_target_product A C hC g 1)).laws
    · simpa only [normalizedReconstructionComparisonData, dif_neg hg, dif_neg hh] using
        (reconstructionBinaryComparison A C hC g h).laws

noncomputable def normalizedReconstructionComparison (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    TensorComparison
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g)
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion h)
      (referenceSimpleRepresentative C hC (simpleOrbitType A g))
      (referenceSimpleRepresentative C hC (simpleOrbitType A h))
      ((reconstructionComponentSystem A C hC).component g).forwardFunctor
      ((reconstructionComponentSystem A C hC).component h).forwardFunctor
      (reconstructionProductEquivalence A C hC g h).forwardFunctor (reconstructionNu A C hC g h) :=
  ⟨normalizedReconstructionComparisonData A C hC g h, normalizedReconstructionComparisonLaws A C hC g h⟩

end RMod.Classification
