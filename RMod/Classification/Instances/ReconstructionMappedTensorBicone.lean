import RMod.Classification.Instances.ReconstructionTensorComponentBicone
import RMod.Classification.Instances.ReconstructionComponents

/-!
# Applying the chosen component equivalence to the tensor presentation

The ordinary composite functor retains the chosen component maps and
forgets only the target span-membership proofs. Mathlib maps the actual
bicone with this functor, keeping its inclusions and projections.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def reconstructionComponentRealization (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :=
  ((reconstructionComponentSystem A C hC).component k).forwardFunctor.toFunctor ⋙
    (InHomogeneousSpan C.toWeaklyPointedSuperfusion
      (referenceSimpleRepresentative C hC (simpleOrbitType A k)).data.object).ι

instance reconstructionComponentRealization_additive (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionComponentRealization A C hC k).Additive := by
  unfold reconstructionComponentRealization
  infer_instance

instance reconstructionComponentRealization_linear (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionComponentRealization A C hC k).Linear ℝ := by
  unfold reconstructionComponentRealization
  infer_instance

noncomputable def reconstructionMappedTensorBicone
    (X Y : LinearCategory A.toWeaklyPointedSuperfusion) (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :=
  (reconstructionComponentRealization A C hC k).mapBicone (reconstructionTensorComponentBicone A X Y k)

end RMod.Classification
