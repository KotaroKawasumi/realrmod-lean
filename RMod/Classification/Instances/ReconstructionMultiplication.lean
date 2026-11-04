import RMod.Classification.Instances.ReconstructionComponents
import RMod.Classification.Instances.ComponentProduct
import RMod.Classification.Proofs.ReferenceSimpleRepresentatives
import RMod.Classification.Proofs.TensorComparisonExistence

/-!
# Binary comparisons for the chosen reconstruction components

The intrinsic product and additive type law identify both product spans
with the chosen component at the group product. The proved comparison
theorem then supplies a unique degree and actual natural invertible maps
on every pair of objects. Cocycle and unit laws are subsequent theorems,
not assumptions on these choices.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstruction_target_product (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    SameParityOrbit C.data.toWeaklyPointedSuperfusionData
      (simpleTensorRepresentative C.toWeaklyPointedSuperfusion
        (referenceSimpleRepresentative C hC (simpleOrbitType A g))
        (referenceSimpleRepresentative C hC (simpleOrbitType A h))).data.object
      (referenceSimpleRepresentative C hC (simpleOrbitType A (g * h))).data.object := by
  rw [simpleOrbitType_mul]
  exact referenceSimpleRepresentative_mul C hC _ _

noncomputable def reconstructionProductEquivalence (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    SpanSuperequivalence A.toWeaklyPointedSuperfusion C.toWeaklyPointedSuperfusion
      (simpleTensorRepresentative A.toWeaklyPointedSuperfusion
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g)
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion h)).data.object
      (simpleTensorRepresentative C.toWeaklyPointedSuperfusion
        (referenceSimpleRepresentative C hC (simpleOrbitType A g))
        (referenceSimpleRepresentative C hC (simpleOrbitType A h))).data.object :=
  componentProductEquivalence (reconstructionComponentSystem A C hC) g h
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g h) (reconstruction_target_product A C hC g h)

theorem exists_unique_reconstructionComparison_parity (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    ∃! a : ZMod 2, Nonempty (TensorComparison
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g)
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion h)
      (referenceSimpleRepresentative C hC (simpleOrbitType A g))
      (referenceSimpleRepresentative C hC (simpleOrbitType A h))
      ((reconstructionComponentSystem A C hC).component g).forwardFunctor
      ((reconstructionComponentSystem A C hC).component h).forwardFunctor
      (reconstructionProductEquivalence A C hC g h).forwardFunctor a) :=
  exists_unique_tensorComparison_parity A C _ _ _ _
    ((reconstructionComponentSystem A C hC).component g)
    ((reconstructionComponentSystem A C hC).component h)
    (reconstructionProductEquivalence A C hC g h)

noncomputable def reconstructionNu (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) : ZMod 2 :=
  (exists_unique_reconstructionComparison_parity A C hC g h).choose

noncomputable def reconstructionBinaryComparison (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    TensorComparison
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g)
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion h)
      (referenceSimpleRepresentative C hC (simpleOrbitType A g))
      (referenceSimpleRepresentative C hC (simpleOrbitType A h))
      ((reconstructionComponentSystem A C hC).component g).forwardFunctor
      ((reconstructionComponentSystem A C hC).component h).forwardFunctor
      (reconstructionProductEquivalence A C hC g h).forwardFunctor (reconstructionNu A C hC g h) :=
  Classical.choice (exists_unique_reconstructionComparison_parity A C hC g h).choose_spec.1

end RMod.Classification
