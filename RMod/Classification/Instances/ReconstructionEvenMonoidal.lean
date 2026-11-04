import RMod.Classification.Instances.MonoidalCoherenceTransport
import RMod.Classification.Proofs.ReconstructionMonoidalComparison

/-!
# Coherence on the already constructed even reconstruction model

The original category supplies pentagon and triangle. Its even equivalence
and the proved comparison diagrams transport those laws to the specified
convolution tensor, associator, and unitors. Omega laws are not inputs.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

@[implicit_reducible]
noncomputable def reconstructionEvenMonoidalCategory (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) :
    letI := reconstructionEvenMonoidalStruct A C hC
    MonoidalCategory
      (EvenSubcategory ℝ (PullbackCategory C.data hC (reconstructionTwistData A C hC))) := by
  letI := reconstructionEvenMonoidalStruct A C hC
  exact monoidalCategoryOfComparison (reconstructionEvenEquivalence A C hC)
    (reconstructionEven_tensorStructuralLaws A C hC) (reconstructionEvenComparison A C hC)

end RMod.Classification
