import RMod.Classification.Instances.PullbackSpanEvaluation
import RMod.Classification.Instances.SpanEquivalenceComposition
import RMod.Classification.Instances.SpanChange
import RMod.Classification.Proofs.PullbackTensorReferenceType

/-!
# Evaluation of the product component with its intrinsic tensor generator

The functor retains coordinate evaluation on objects and morphisms. Only
the certificate of membership changes to the product reference span.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (S T : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def pullbackTensorEvaluation :
    SpanSuperequivalence (twistedPullback C hC t).toWeaklyPointedSuperfusion
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (simpleTensorRepresentative (twistedPullback C hC t).toWeaklyPointedSuperfusion S T).data.object
      (simpleTensorRepresentative
        ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
        (pullbackReferenceSimple C hC t S) (pullbackReferenceSimple C hC t T)).data.object :=
  (pullbackSpanEvaluationEquivalence C hC t
    (simpleTensorRepresentative (twistedPullback C hC t).toWeaklyPointedSuperfusion S T)).trans
    (spanChangeSuperequivalence
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (inHomogeneousSpan_congr_generator
        ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
        (pullbackReferenceSimple C hC t
          (simpleTensorRepresentative (twistedPullback C hC t).toWeaklyPointedSuperfusion S T)).laws.simple
        (simpleTensorRepresentative
          ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
          (pullbackReferenceSimple C hC t S) (pullbackReferenceSimple C hC t T)).laws.simple
        (pullbackTensorReference_sameOrbit C hC t S T)))

end RMod.Classification
