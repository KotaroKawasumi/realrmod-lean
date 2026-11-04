import RMod.Classification.Proofs.EquivalenceTensorComparison

/-! # The completed binary comparison of an arbitrary model equivalence -/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def equivalenceTensorComparison
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (S T : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion) :
    TensorComparison S T (pullbackReferenceSimple C hC s S) (pullbackReferenceSimple C hC s T)
      (equivalenceEvaluatedComponent C hC s t E S).forwardFunctor
      (equivalenceEvaluatedComponent C hC s t E T).forwardFunctor
      (equivalenceTensorEvaluation C hC s t E S T).forwardFunctor
      (t.data.nu (pullbackSimpleDegree C hC t (E.mapSimple S))
        (pullbackSimpleDegree C hC t (E.mapSimple T))) :=
  ⟨equivalenceTensorComparisonData C hC s t E S T,
    equivalenceTensorComparisonLaws C hC s t E S T⟩

end RMod.Classification
