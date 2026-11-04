import RMod.Classification.Instances.ReconstructionMonoidalComparison
import RMod.Classification.Proofs.ConvolutionEvenStructureOfParity
import RMod.Classification.Proofs.ReconstructionTensoratorNaturality
import RMod.Classification.Proofs.ReconstructionAssociativity
import RMod.Classification.Proofs.ReconstructionUnitCoherence

/-!
# The proved reconstruction diagrams form a monoidal comparison

This packages exactly the previously established global diagrams. The
formation structure on the target still has no pentagon or triangle;
those will follow by transport from the original category.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstructionEven_tensorStructuralLaws :
    letI := reconstructionEvenMonoidalStruct A C hC
    TensorStructuralLaws
      (EvenSubcategory ℝ (PullbackCategory C.data hC (reconstructionTwistData A C hC))) :=
  convolutionEven_tensorStructuralLawsOfParity C.data hC (reconstructionTwistData A C hC)
    (reconstruction_normalizer_parity A C hC) (reconstructionNu_one_left A C hC)
    (reconstructionNu_one_right A C hC)

theorem reconstructionEvenComparisonLaws :
    letI := reconstructionEvenMonoidalStruct A C hC
    MonoidalComparisonLaws (reconstructionEvenEquivalence A C hC).functor
      (reconstructionEvenComparisonData A C hC) := by
  letI := reconstructionEvenMonoidalStruct A C hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X X' Y Y' f g
    apply WideSubcategory.hom_ext
    funext q
    exact reconstructionTensorator_naturality A C hC f.hom g.hom q
  · intro X Y Z
    apply WideSubcategory.hom_ext
    funext q
    exact (C.laws.comp_assoc _ _ _).symm.trans
      (reconstructionTensorator_associativity A C hC X.obj Y.obj Z.obj q)
  · intro X
    apply WideSubcategory.hom_ext
    funext q
    exact (C.laws.comp_assoc _ _ _).symm.trans
      (reconstructionTensorator_left_unit A C hC X.obj q)
  · intro X
    apply WideSubcategory.hom_ext
    funext q
    exact (C.laws.comp_assoc _ _ _).symm.trans
      (reconstructionTensorator_right_unit A C hC X.obj q)

noncomputable def reconstructionEvenComparison :
    letI := reconstructionEvenMonoidalStruct A C hC
    MonoidalComparison (reconstructionEvenEquivalence A C hC).functor := by
  letI := reconstructionEvenMonoidalStruct A C hC
  exact ⟨reconstructionEvenComparisonData A C hC, reconstructionEvenComparisonLaws A C hC⟩

end RMod.Classification
