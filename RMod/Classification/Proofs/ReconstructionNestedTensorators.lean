import RMod.Classification.Proofs.ReconstructionOuterTensorator
import RMod.Classification.Proofs.ReconstructionTripleTensoratorFormula
import RMod.Classification.Proofs.TensorWhiskerCalculus

/-!
# Combining the actual binary reconstruction maps on three components

Move the inner mapped inclusion through the outer tensorator. The
remaining composite is exactly the component triple tensorator followed
by the retained triple inclusion. Identity whiskerings introduce no
interchange sign.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionNestedTensorator_left :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom
        (C.data.comp
          ((reconstructionTensorComparison A C hC g h).data.app
            ((reconstructionSourceEquivalence A).inverse.obj X g)
            ((reconstructionSourceEquivalence A).inverse.obj Y h)).hom
          (reconstructionMappedTensorSpanInclusion A C hC X Y g h))
        (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj Z) k).val))
        (C.data.id (C.data.pi.factor (reconstructionNu A C hC (g * h) k))))
      ((reconstructionTensorComparison A C hC (g * h) k).data.app
        ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X Y) (g * h))
        ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom)
      (reconstructionMappedTensorSpanInclusion A C hC (A.data.tensorObj X Y) Z (g * h) k) =
    C.data.comp
      (componentTripleLeftTensorator
        (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
        (reconstructionComponentSystem A C hC)
        (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion)
        (reconstruction_target_product A C hC) (reconstructionNu A C hC)
        (normalizedReconstructionComparison A C hC) g h k
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y h)
        ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom
      (reconstructionMappedTripleLeftInclusion A C hC X Y Z g h k) := by
  rw [reconstructionTripleLeftTensorator_hom,
    tensor_right_right_comp C.laws.toWeaklyPointedSuperfusionLaws]
  have hc := congrArg (C.data.comp
      (C.data.tensorHom (C.data.tensorHom
        ((reconstructionTensorComparison A C hC g h).data.app
          ((reconstructionSourceEquivalence A).inverse.obj X g)
          ((reconstructionSourceEquivalence A).inverse.obj Y h)).hom
        (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj Z) k).val))
        (C.data.id (C.data.pi.factor (reconstructionNu A C hC (g * h) k)))))
      (reconstructionOuterTensorator_left_inclusion A C hC X Y Z g h k)
  exact (congrArg (fun m => C.data.comp m
      (reconstructionMappedTensorSpanInclusion A C hC (A.data.tensorObj X Y) Z (g * h) k))
      (C.laws.comp_assoc _ _ _)).trans
    ((C.laws.comp_assoc _ _ _).trans
      (hc.trans (C.laws.comp_assoc _ _ _).symm))

theorem reconstructionNestedTensorator_right :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom
        (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)
        (C.data.comp
          ((reconstructionTensorComparison A C hC h k).data.app
            ((reconstructionSourceEquivalence A).inverse.obj Y h)
            ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom
          (reconstructionMappedTensorSpanInclusion A C hC Y Z h k)))
        (C.data.id (C.data.pi.factor (reconstructionNu A C hC g (h * k)))))
      ((reconstructionTensorComparison A C hC g (h * k)).data.app
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj Y Z) (h * k))).hom)
      (reconstructionMappedTensorSpanInclusion A C hC X (A.data.tensorObj Y Z) g (h * k)) =
    C.data.comp
      (componentTripleRightTensorator
        (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
        (reconstructionComponentSystem A C hC)
        (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion)
        (reconstruction_target_product A C hC) (reconstructionNu A C hC)
        (normalizedReconstructionComparison A C hC) g h k
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y h)
        ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom
      (reconstructionMappedTripleRightInclusion A C hC X Y Z g h k) := by
  rw [reconstructionTripleRightTensorator_hom,
    tensor_left_right_comp C.laws.toWeaklyPointedSuperfusionLaws]
  have hc := congrArg (C.data.comp
      (C.data.tensorHom (C.data.tensorHom
        (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)
        ((reconstructionTensorComparison A C hC h k).data.app
          ((reconstructionSourceEquivalence A).inverse.obj Y h)
          ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom)
        (C.data.id (C.data.pi.factor (reconstructionNu A C hC g (h * k))))))
      (reconstructionOuterTensorator_right_inclusion A C hC X Y Z g h k)
  exact (congrArg (fun m => C.data.comp m
      (reconstructionMappedTensorSpanInclusion A C hC X (A.data.tensorObj Y Z) g (h * k)))
      (C.laws.comp_assoc _ _ _)).trans
    ((C.laws.comp_assoc _ _ _).trans
      (hc.trans (C.laws.comp_assoc _ _ _).symm))

end RMod.Classification
