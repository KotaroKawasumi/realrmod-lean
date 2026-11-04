import RMod.Classification.Instances.ReconstructionEvenEquivalence
import RMod.Classification.Instances.ConvolutionEvenStructureOfParity
import RMod.Classification.Proofs.ReconstructionTensorator
import RMod.Classification.Proofs.ReconstructionUnit
import RMod.Classification.Proofs.ReconstructionParity
import RMod.Classification.Abstract.MonoidalComparison

/-! # The actual reconstruction comparisons on the even categories -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

@[implicit_reducible]
noncomputable def reconstructionEvenMonoidalStruct :
    MonoidalCategoryStruct
      (EvenSubcategory ℝ (PullbackCategory C.data hC (reconstructionTwistData A C hC))) :=
  convolutionEvenMonoidalStructOfParity C.data hC (reconstructionTwistData A C hC)
    (reconstruction_normalizer_parity A C hC) (reconstructionNu_one_left A C hC)
    (reconstructionNu_one_right A C hC)

noncomputable def reconstructionEvenComparisonData :
    letI := reconstructionEvenMonoidalStruct A C hC
    MonoidalComparisonData (reconstructionEvenEquivalence A C hC).functor := by
  letI := reconstructionEvenMonoidalStruct A C hC
  exact
    { tensor X Y :=
        { hom := ⟨fun q => (reconstructionTensoratorData A C hC X.obj Y.obj q).hom,
            fun q => (reconstructionTensorator_evenIso A C hC X.obj Y.obj q).hom_even⟩
          inv := ⟨fun q => (reconstructionTensoratorData A C hC X.obj Y.obj q).inv,
            fun q => (reconstructionTensorator_evenIso A C hC X.obj Y.obj q).inv_even⟩
          hom_inv_id := by
            apply WideSubcategory.hom_ext
            funext q
            exact (reconstructionTensorator_evenIso A C hC X.obj Y.obj q).hom_inv
          inv_hom_id := by
            apply WideSubcategory.hom_ext
            funext q
            exact (reconstructionTensorator_evenIso A C hC X.obj Y.obj q).inv_hom }
      unit :=
        { hom := ⟨fun q => (reconstructionUnitData A C hC q).hom,
            fun q => (reconstructionUnit_evenIso A C hC q).hom_even⟩
          inv := ⟨fun q => (reconstructionUnitData A C hC q).inv,
            fun q => (reconstructionUnit_evenIso A C hC q).inv_even⟩
          hom_inv_id := by
            apply WideSubcategory.hom_ext
            funext q
            exact (reconstructionUnit_evenIso A C hC q).hom_inv
          inv_hom_id := by
            apply WideSubcategory.hom_ext
            funext q
            exact (reconstructionUnit_evenIso A C hC q).inv_hom } }

end RMod.Classification
