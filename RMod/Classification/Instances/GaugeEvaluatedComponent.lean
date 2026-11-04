import RMod.Classification.Instances.GaugeComponentParity
import RMod.Classification.Instances.SpanComparisonTransfer

/-!
# The equivalence's component maps compared with direct evaluation

Both functors now have the original model component as their source.
Their selected comparison is invertible and signed-natural on every
homogeneous morphism. This is the form used to transport tensorators.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def equivalenceEvaluatedComponent
    (S : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion) :
    SpanSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      S.data.object (S.data.object (pullbackSimpleDegree C hC s S)).val :=
  ((E.spanRestriction S).trans
    (pullbackSpanEvaluationEquivalence C hC t (E.mapSimple S))).trans
      (spanChangeSuperequivalence ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
        (fun X => (inHomogeneousSpan_congr_generator
          ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
          (pullbackSimpleDegree_simple C hC s S) (pullbackSimpleDegree_simple C hC t (E.mapSimple S))
          (equivalenceComponentGenerators_sameOrbit C hC s t E S) X).symm))

noncomputable def equivalenceComponentComparison (g : s.data.group) :
    SpanHomogeneousNatIso
      (equivalenceEvaluatedComponent C hC s t E (pullbackDegreeSimple C hC s g)).forwardFunctor
      (pullbackSpanEvaluationEquivalence C hC s (pullbackDegreeSimple C hC s g)).forwardFunctor
      (equivalenceGaugeLambda C hC s t E g) :=
  (pullbackSpanEvaluationEquivalence C hC s (pullbackDegreeSimple C hC s g)).comparisonTransfer
    (equivalenceEvaluatedComponent C hC s t E (pullbackDegreeSimple C hC s g))
    (equivalenceReferenceComparison C hC s t E g)

end RMod.Classification
