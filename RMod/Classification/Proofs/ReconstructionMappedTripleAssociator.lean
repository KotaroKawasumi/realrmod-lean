import RMod.Classification.Proofs.ReconstructionTripleSpanMaps
import RMod.Classification.Instances.ReconstructionMappedTripleComponents

/-!
# The mapped source associator on the actual triple presentation

Apply the component realization to the full-subcategory equation. Its
image of the selected component map is exactly the coordinate of the
global reconstruction functor's image of the ambient associator.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionMappedTripleInclusion_associator_at_left :
    C.data.comp (reconstructionMappedTripleLeftInclusion A C hC X Y Z g h k)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map
        (A.data.associatorHom X Y Z) ((g * h) * k)) =
    C.data.comp
      ((reconstructionComponentRealization A C hC ((g * h) * k)).map
        (reconstructionTripleAssociatorAtLeft A X Y Z g h k))
      ((reconstructionComponentRealization A C hC ((g * h) * k)).map
        (reconstructionTripleRightInclusionAtLeft A X Y Z g h k)) := by
  let F := reconstructionComponentRealization A C hC ((g * h) * k)
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (reconstructionTripleInclusion_associator_at_left A X Y Z g h k)).trans
      (F.map_comp _ _))

end RMod.Classification
