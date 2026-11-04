import RMod.Classification.Instances.GaugeSimpleComparison
import RMod.Classification.Instances.EquivalenceTensorEvaluation

/-!
# The output comparison on the intrinsic product component

The tensor constituent uses the same selected comparison as its support.
Changing only the reference generator puts it between the two product
evaluation functors, with precisely the selected product parity.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def equivalenceTensorComponentComparison
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (S T : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion) :
    SpanHomogeneousNatIso (equivalenceTensorEvaluation C hC s t E S T).forwardFunctor
      (pullbackTensorEvaluation C hC s S T).forwardFunctor
      (equivalenceGaugeLambda C hC s t E
        (pullbackSimpleDegree C hC s
          (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T))) :=
  (equivalenceSimpleComparison C hC s t E
    (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T) _ rfl).postcompose
    (spanChangeSuperequivalence
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (inHomogeneousSpan_congr_generator
        ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
        (pullbackReferenceSimple C hC s
          (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T)).laws.simple
        (simpleTensorRepresentative
          ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
          (pullbackReferenceSimple C hC s S) (pullbackReferenceSimple C hC s T)).laws.simple
        (pullbackTensorReference_sameOrbit C hC s S T))).forwardFunctor

end RMod.Classification
