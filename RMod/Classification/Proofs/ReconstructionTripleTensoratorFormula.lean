import RMod.Classification.Instances.ComponentTripleTensorators
import RMod.Classification.Instances.ReconstructionMappedTripleComponents
import RMod.Classification.Instances.ReconstructionOmega

/-!
# The component triple tensorators use the selected reconstruction maps

Reindexing the tensor generators changes span-membership proofs only.
Consequently the underlying maps of the component triple tensorators
are the composites of the two selected binary reconstruction maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTripleLeftTensorator_hom :
    (componentTripleLeftTensorator
      (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
      (reconstructionComponentSystem A C hC)
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion)
      (reconstruction_target_product A C hC) (reconstructionNu A C hC)
      (normalizedReconstructionComparison A C hC) g h k
      ((reconstructionSourceEquivalence A).inverse.obj X g)
      ((reconstructionSourceEquivalence A).inverse.obj Y h)
      ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom =
    C.data.comp
      (C.data.tensorHom (C.data.tensorHom
        ((reconstructionTensorComparison A C hC g h).data.app
          ((reconstructionSourceEquivalence A).inverse.obj X g)
          ((reconstructionSourceEquivalence A).inverse.obj Y h)).hom
        (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj Z) k).val))
        (C.data.id (C.data.pi.factor (reconstructionNu A C hC (g * h) k))))
      ((reconstructionTensorComparison A C hC (g * h) k).data.app
        (reconstructionTensorSpanObject A X Y g h)
        ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom := rfl

theorem reconstructionTripleRightTensorator_hom :
    (componentTripleRightTensorator
      (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
      (reconstructionComponentSystem A C hC)
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion)
      (reconstruction_target_product A C hC) (reconstructionNu A C hC)
      (normalizedReconstructionComparison A C hC) g h k
      ((reconstructionSourceEquivalence A).inverse.obj X g)
      ((reconstructionSourceEquivalence A).inverse.obj Y h)
      ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom =
    C.data.comp
      (C.data.tensorHom (C.data.tensorHom
        (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)
        ((reconstructionTensorComparison A C hC h k).data.app
          ((reconstructionSourceEquivalence A).inverse.obj Y h)
          ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom)
        (C.data.id (C.data.pi.factor (reconstructionNu A C hC g (h * k)))))
      ((reconstructionTensorComparison A C hC g (h * k)).data.app
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        (reconstructionTensorSpanObject A Y Z h k)).hom := rfl

end RMod.Classification
