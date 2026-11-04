import RMod.Classification.Proofs.ReconstructionSelectedUnitCoherence
import RMod.Classification.Proofs.ReconstructionTensorComparisonUnit

/-!
# The actual extracted parity degree in the selected unit diagram

The extracted degree is proved to be zero. Transport its right parity
factor and use equality of the chosen comparison data with the canonical
unit comparison. This preserves the actual reconstruction tensorator.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionLeftUnitParity_coherence :
    C.data.comp
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (congrArg (fun q => C.data.tensorObj (C.data.tensorObj C.data.tensorUnit (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) (C.data.pi.factor q))
          (reconstructionNu_one_left A C hC g))).inv
      (C.data.comp (C.data.comp
        (C.data.tensorHom (C.data.tensorHom (reconstructionNeutralUnitData A C hC).hom (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)) (C.data.id (C.data.pi.factor (reconstructionNu A C hC 1 g))))
        ((reconstructionTensorComparison A C hC 1 g).data.app ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1) ((reconstructionSourceEquivalence A).inverse.obj X g)).hom)
        (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
            (reconstructionLeftUnitComponent_obj A C hC X g)).hom
          ((reconstructionComponentRealization A C hC g).map (reconstructionLeftUnitSpanMap A X g)))) =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)) (C.data.leftUnitorHom (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) := by
  have hp := parityTensorComparison_inserted_of_data_eq
    (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (normalizedReconstructionComparison A C hC 1 g)
    ((reconstructionComponentSystem A C hC).leftUnitComparison g
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion 1 g)
      (reconstruction_target_product A C hC 1 g))
    (reconstructionNu_one_left A C hC g) (normalizedReconstructionComparison_one_left A C hC g)
    ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1) ((reconstructionSourceEquivalence A).inverse.obj X g) (C.data.tensorHom (reconstructionNeutralUnitData A C hC).hom (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val))
  exact (C.laws.comp_assoc _ _ _).symm.trans
    ((congrArg (fun f => C.data.comp f
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
          (reconstructionLeftUnitComponent_obj A C hC X g)).hom
        ((reconstructionComponentRealization A C hC g).map (reconstructionLeftUnitSpanMap A X g)))) hp).trans
      (reconstructionLeftSelectedUnit_coherence A C hC X g))

theorem reconstructionRightUnitParity_coherence :
    C.data.comp
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (congrArg (fun q => C.data.tensorObj (C.data.tensorObj (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val C.data.tensorUnit) (C.data.pi.factor q))
          (reconstructionNu_one_right A C hC g))).inv
      (C.data.comp (C.data.comp
        (C.data.tensorHom (C.data.tensorHom (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) (reconstructionNeutralUnitData A C hC).hom) (C.data.id (C.data.pi.factor (reconstructionNu A C hC g 1))))
        ((reconstructionTensorComparison A C hC g 1).data.app ((reconstructionSourceEquivalence A).inverse.obj X g) ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1)).hom)
        (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
            (reconstructionRightUnitComponent_obj A C hC X g)).hom
          ((reconstructionComponentRealization A C hC g).map (reconstructionRightUnitSpanMap A X g)))) =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val C.data.tensorUnit)) (C.data.rightUnitorHom (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) := by
  have hp := parityTensorComparison_inserted_of_data_eq
    (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (normalizedReconstructionComparison A C hC g 1)
    ((reconstructionComponentSystem A C hC).rightUnitComparison g
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g 1)
      (reconstruction_target_product A C hC g 1))
    (reconstructionNu_one_right A C hC g) (normalizedReconstructionComparison_one_right A C hC g)
    ((reconstructionSourceEquivalence A).inverse.obj X g) ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1) (C.data.tensorHom (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) (reconstructionNeutralUnitData A C hC).hom)
  exact (C.laws.comp_assoc _ _ _).symm.trans
    ((congrArg (fun f => C.data.comp f
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
          (reconstructionRightUnitComponent_obj A C hC X g)).hom
        ((reconstructionComponentRealization A C hC g).map (reconstructionRightUnitSpanMap A X g)))) hp).trans
      (reconstructionRightSelectedUnit_coherence A C hC X g))

end RMod.Classification
