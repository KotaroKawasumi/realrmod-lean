import RMod.Classification.Proofs.ReconstructionTripleRealizationIndex
import RMod.Classification.Instances.ComponentTripleTensorators
import RMod.Classification.Instances.ReconstructionMultiplication

/-!
# The extracted component associator uses the same retained index map

Unfolding the component reindexings leaves their original ambient maps.
The comparison used to extract omega is therefore the product-index
equality followed by the selected component image of the source associator.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionComponentAssociator_hom :
    (componentMappedTripleAssociator (reconstructionComponentSystem A C hC)
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion) (reconstruction_target_product A C hC)
      g h k ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y h)
        ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom =
    C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
      (reconstructionTripleLeftRealization_index A C hC X Y Z g h k)).hom
      ((reconstructionComponentRealization A C hC (g * (h * k))).map
        (reconstructionTripleAssociatorAtRight A X Y Z g h k)) := rfl

end RMod.Classification
