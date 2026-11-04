import RMod.Classification.Instances.ReconstructionSuperequivalenceData
import RMod.Classification.Proofs.ReconstructionUnderlyingEquivalence
import RMod.Classification.Proofs.ReconstructionTensorator
import RMod.Classification.Proofs.ReconstructionUnit
import RMod.Classification.Proofs.ReconstructionTensoratorNaturality
import RMod.Classification.Proofs.ReconstructionUnitCoherence
import RMod.Classification.Proofs.ReconstructionAssociativity

/-!
# All laws of the specified reconstruction superequivalence

The ordinary equivalence supplies inverse identities and naturality.
Its proved superlinearity and the global tensorator diagrams supply the
remaining laws, including naturality on odd morphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstructionMonoidalFunctorLaws :
    MonoidalSuperfunctorLaws A.data.toWeaklyPointedSuperfusionData
      (reconstructionModelData A C hC).toWeaklyPointedSuperfusionData
      (reconstructionMonoidalFunctorData A C hC) where
  map_id := (reconstructionUnderlyingEquivalence A C hC).functor.map_id
  map_comp := (reconstructionUnderlyingEquivalence A C hC).functor.map_comp
  map_zero X Y := (reconstructionUnderlyingEquivalence A C hC).functor.map_zero X Y
  map_add _ _ := (reconstructionUnderlyingEquivalence A C hC).functor.map_add
  map_smul := (reconstructionUnderlyingEquivalence A C hC).functor.map_smul
  map_grade f hf := reconstructionUnderlying_forward_grade A C hC f hf
  tensor_hom_even X Y := fun q => (reconstructionTensorator_evenIso A C hC X Y q).hom_even
  tensor_inv_even X Y := fun q => (reconstructionTensorator_evenIso A C hC X Y q).inv_even
  tensor_hom_inv X Y := funext fun q => (reconstructionTensorator_evenIso A C hC X Y q).hom_inv
  tensor_inv_hom X Y := funext fun q => (reconstructionTensorator_evenIso A C hC X Y q).inv_hom
  unit_hom_even := fun q => (reconstructionUnit_evenIso A C hC q).hom_even
  unit_inv_even := fun q => (reconstructionUnit_evenIso A C hC q).inv_even
  unit_hom_inv := funext fun q => (reconstructionUnit_evenIso A C hC q).hom_inv
  unit_inv_hom := funext fun q => (reconstructionUnit_evenIso A C hC q).inv_hom
  tensor_naturality f g := funext fun q => reconstructionTensorator_naturality A C hC f g q
  associativity X Y Z := by
    funext q
    exact (reconstructionTensorator_associativity A C hC X Y Z q).trans
      (C.laws.comp_assoc _ _ _).symm
  left_unit X := funext fun q => reconstructionTensorator_left_unit A C hC X q
  right_unit X := funext fun q => reconstructionTensorator_right_unit A C hC X q

theorem reconstructionSuperequivalenceLaws :
    MonoidalSuperequivalenceLaws A.data.toWeaklyPointedSuperfusionData
      (reconstructionModelData A C hC).toWeaklyPointedSuperfusionData
      (reconstructionSuperequivalenceData A C hC) where
  forward := reconstructionMonoidalFunctorLaws A C hC
  backward :=
    { map_id := (reconstructionUnderlyingEquivalence A C hC).inverse.map_id
      map_comp := (reconstructionUnderlyingEquivalence A C hC).inverse.map_comp
      map_zero X Y := (reconstructionUnderlyingEquivalence A C hC).inverse.map_zero X Y
      map_add _ _ := (reconstructionUnderlyingEquivalence A C hC).inverse.map_add
      map_smul := (reconstructionUnderlyingEquivalence A C hC).inverse.map_smul
      map_grade f hf := reconstructionUnderlying_backward_grade A C hC f hf }
  unit_hom_even := reconstructionUnderlying_unit_hom_even A C hC
  unit_inv_even := reconstructionUnderlying_unit_inv_even A C hC
  unit_hom_inv X := (reconstructionUnderlyingEquivalence A C hC).unitIso.hom_inv_id_app X
  unit_inv_hom X := (reconstructionUnderlyingEquivalence A C hC).unitIso.inv_hom_id_app X
  counit_hom_even := reconstructionUnderlying_counit_hom_even A C hC
  counit_inv_even := reconstructionUnderlying_counit_inv_even A C hC
  counit_hom_inv X := (reconstructionUnderlyingEquivalence A C hC).counitIso.hom_inv_id_app X
  counit_inv_hom X := (reconstructionUnderlyingEquivalence A C hC).counitIso.inv_hom_id_app X
  unit_naturality f := (reconstructionUnderlyingEquivalence A C hC).unitIso.hom.naturality f
  counit_naturality f := (reconstructionUnderlyingEquivalence A C hC).counitIso.hom.naturality f

end RMod.Classification
