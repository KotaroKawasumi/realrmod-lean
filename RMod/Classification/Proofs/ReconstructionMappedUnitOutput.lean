import RMod.Classification.Proofs.ReconstructionUnitOutputMaps
import RMod.Classification.Instances.ReconstructionMappedTensorBicone

/-!
# The mapped unit presentation and the global reconstruction functor

Apply the selected component functor to the source presentation equation.
Mathlib functoriality retains the same equality map and turns the source
unitor into the actual coordinate of the global reconstruction map.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionMappedLeftUnitOutput_map :
    C.data.comp ((reconstructionMappedTensorBicone A C hC A.data.tensorUnit X g).ι 1)
      (((reconstructionUnderlyingEquivalence A C hC).functor.map (A.data.leftUnitorHom X)) g) =
      C.data.comp
        (@eqToHom (LinearCategory C.toWeaklyPointedSuperfusion) _ _ _
          (congrArg (reconstructionComponentRealization A C hC g).obj (reconstructionLeftUnitOutput_eq A X g)))
        ((reconstructionComponentRealization A C hC g).map (reconstructionLeftUnitSpanMap A X g)) := by
  let F := reconstructionComponentRealization A C hC g
  have h := congrArg F.map (reconstructionLeftUnitOutput_map A X g)
  rw [F.map_comp, F.map_comp, eqToHom_map] at h
  exact h

theorem reconstructionMappedRightUnitOutput_map :
    C.data.comp ((reconstructionMappedTensorBicone A C hC X A.data.tensorUnit g).ι g)
      (((reconstructionUnderlyingEquivalence A C hC).functor.map (A.data.rightUnitorHom X)) g) =
      C.data.comp
        (@eqToHom (LinearCategory C.toWeaklyPointedSuperfusion) _ _ _
          (congrArg (reconstructionComponentRealization A C hC g).obj (reconstructionRightUnitOutput_eq A X g)))
        ((reconstructionComponentRealization A C hC g).map (reconstructionRightUnitSpanMap A X g)) := by
  let F := reconstructionComponentRealization A C hC g
  have h := congrArg F.map (reconstructionRightUnitOutput_map A X g)
  rw [F.map_comp, F.map_comp, eqToHom_map] at h
  exact h

end RMod.Classification
