import RMod.Classification.Instances.GaugeEvaluatedComponent
import RMod.Classification.Instances.PullbackTensorEvaluation

/-!
# The product-component functor of an arbitrary monoidal equivalence

Evaluate the image at its support and identify the reference product span
by intrinsic type. As for direct evaluation, the latter operation changes
only membership certificates and retains every actual map.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def equivalenceTensorEvaluation
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (S T : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion) :
    SpanSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T).data.object
      (simpleTensorRepresentative
        ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
        (pullbackReferenceSimple C hC s S) (pullbackReferenceSimple C hC s T)).data.object :=
  (equivalenceEvaluatedComponent C hC s t E
    (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T)).trans
    (spanChangeSuperequivalence
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (inHomogeneousSpan_congr_generator
        ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
        (pullbackReferenceSimple C hC s
          (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T)).laws.simple
        (simpleTensorRepresentative
          ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
          (pullbackReferenceSimple C hC s S) (pullbackReferenceSimple C hC s T)).laws.simple
        (pullbackTensorReference_sameOrbit C hC s S T)))

end RMod.Classification
