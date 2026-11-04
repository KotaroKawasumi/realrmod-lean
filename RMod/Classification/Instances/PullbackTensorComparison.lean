import RMod.Classification.Proofs.PullbackTensorComparison

/-! # The completed binary comparison of the pullback evaluation functors -/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def pullbackTensorComparison
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
    (S T : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    TensorComparison S T (pullbackReferenceSimple C hC t S) (pullbackReferenceSimple C hC t T)
      (pullbackSpanEvaluationEquivalence C hC t S).forwardFunctor
      (pullbackSpanEvaluationEquivalence C hC t T).forwardFunctor
      (pullbackTensorEvaluation C hC t S T).forwardFunctor
      (t.data.nu (pullbackSimpleDegree C hC t S) (pullbackSimpleDegree C hC t T)) :=
  ⟨pullbackTensorComparisonData C hC t S T, pullbackTensorComparisonLaws C hC t S T⟩

end RMod.Classification
