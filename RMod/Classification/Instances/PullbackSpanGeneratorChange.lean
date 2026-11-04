import RMod.Classification.Proofs.PullbackReferenceGeneratorChange
import RMod.Classification.Instances.SpanChange

/-!
# Changing generators with a fixed support

Both the model span and its reference span change by identity functors
on ambient objects and morphisms. The equality of supports supplies the
required homogeneous orbit comparisons; the inverse maps remain identity.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (S T : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion)
  (e : pullbackSimpleDegree C hC t S = pullbackSimpleDegree C hC t T)

noncomputable def pullbackSourceSpanChange :
    SpanSuperequivalence (twistedPullback C hC t).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion S.data.object T.data.object :=
  spanChangeSuperequivalence (twistedPullback C hC t).toWeaklyPointedSuperfusion
    (inHomogeneousSpan_congr_generator (twistedPullback C hC t).toWeaklyPointedSuperfusion
      S.laws.simple T.laws.simple ((pullbackSimpleDegree_eq_iff C hC t S T).mp e))

noncomputable def pullbackReferenceSpanChange :
    SpanSuperequivalence
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (pullbackReferenceSimple C hC t S).data.object (pullbackReferenceSimple C hC t T).data.object :=
  spanChangeSuperequivalence ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (inHomogeneousSpan_congr_generator
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (pullbackReferenceSimple C hC t S).laws.simple (pullbackReferenceSimple C hC t T).laws.simple
      (pullbackReference_sameOrbit_of_degree_eq C hC t S T e))

end RMod.Classification
