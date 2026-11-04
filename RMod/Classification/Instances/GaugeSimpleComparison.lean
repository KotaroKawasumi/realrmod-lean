import RMod.Classification.Instances.SpanNaturalWhiskering
import RMod.Classification.Proofs.PullbackEvaluationGeneratorChange

/-!
# The selected parity comparison on any simple with the same support

Change to the selected simple, apply its retained comparison, and change
the reference generator back. Equality of the actual evaluation functors
identifies the endpoints. No new choice of parity or comparison is made.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def equivalenceSimpleComparison
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (S : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion) (g : s.data.group)
    (hg : pullbackSimpleDegree C hC s S = g) :
    SpanHomogeneousNatIso (equivalenceEvaluatedComponent C hC s t E S).forwardFunctor
      (pullbackSpanEvaluationEquivalence C hC s S).forwardFunctor
      (equivalenceGaugeLambda C hC s t E g) := by
  let P := pullbackDegreeSimple C hC s g
  have e : pullbackSimpleDegree C hC s S = pullbackSimpleDegree C hC s P :=
    hg.trans (pullbackSimpleDegree_placed C hC s g).symm
  have η := ((equivalenceComponentComparison C hC s t E g).precompose
    (pullbackSourceSpanChange C hC s S P e).forwardFunctor).postcompose
      (pullbackReferenceSpanChange C hC s P S e.symm).forwardFunctor
  rw [equivalenceEvaluation_change_generator C hC s S P e t E,
    pullbackEvaluation_change_generator C hC s S P e] at η
  exact η

end RMod.Classification
