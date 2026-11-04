import RMod.Classification.Instances.ReconstructionTripleComponents
import RMod.Classification.Instances.ReconstructionMappedTensorBicone
import RMod.Classification.Instances.ReconstructionUnderlyingEquivalence

/-!
# Actual component images of the binary and triple source inclusions

The chosen component realization maps these full-subcategory morphisms.
The codomains are exactly the corresponding coordinates of the global
reconstruction functor, with each parenthesization retaining its product
index.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionMappedTensorSpanInclusion :
    C.data.Hom ((reconstructionComponentRealization A C hC (g * h)).obj
      (reconstructionTensorSpanObject A X Y g h))
      (((reconstructionUnderlyingEquivalence A C hC).functor.obj (A.data.tensorObj X Y)) (g * h)).val :=
  (reconstructionComponentRealization A C hC (g * h)).map (reconstructionTensorSpanInclusion A X Y g h)

noncomputable def reconstructionMappedTripleLeftInclusion :
    C.data.Hom ((reconstructionComponentRealization A C hC ((g * h) * k)).obj
      (reconstructionTripleLeftSpan A X Y Z g h k))
      (((reconstructionUnderlyingEquivalence A C hC).functor.obj
        (A.data.tensorObj (A.data.tensorObj X Y) Z)) ((g * h) * k)).val :=
  (reconstructionComponentRealization A C hC ((g * h) * k)).map
    (reconstructionTripleLeftInclusion A X Y Z g h k)

noncomputable def reconstructionMappedTripleRightInclusion :
    C.data.Hom ((reconstructionComponentRealization A C hC (g * (h * k))).obj
      (reconstructionTripleRightSpan A X Y Z g h k))
      (((reconstructionUnderlyingEquivalence A C hC).functor.obj
        (A.data.tensorObj X (A.data.tensorObj Y Z))) (g * (h * k))).val :=
  (reconstructionComponentRealization A C hC (g * (h * k))).map
    (reconstructionTripleRightInclusion A X Y Z g h k)

end RMod.Classification
