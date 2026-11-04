import RMod.Classification.Instances.GaugeTensorComponentComparison
import RMod.Classification.Instances.EquivalenceTensorComparison
import RMod.Classification.Instances.PullbackTensorComparison
import RMod.Classification.Proofs.TensorComparisonChangeParity

/-!
# Every monoidal equivalence forces the binary parity gauge equation

Transport its actual binary comparison by the three selected component
comparisons. Uniqueness compares the resulting degree with direct support
evaluation. The two contributions of each parity cancel in Z/2, yielding
nu' pulled back by phi equals nu plus the coboundary of lambda.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem equivalenceGaugeLambda_nu
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion) (g h : s.data.group) :
    t.data.nu (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h) =
      s.data.nu g h + equivalenceGaugeLambda C hC s t E h +
        equivalenceGaugeLambda C hC s t E (g * h) + equivalenceGaugeLambda C hC s t E g := by
  let S := pullbackDegreeSimple C hC s g
  let T := pullbackDegreeSimple C hC s h
  have he := TensorComparison.component_change_parity
    (pullbackSpanEvaluationEquivalence C hC s S) (pullbackSpanEvaluationEquivalence C hC s T)
    (equivalenceTensorComparison C hC s t E S T)
    (equivalenceComponentComparison C hC s t E g) (equivalenceComponentComparison C hC s t E h)
    (equivalenceTensorComponentComparison C hC s t E S T) (pullbackTensorComparison C hC s S T)
  dsimp only [S, T] at he
  rw [pullbackSimpleDegree_tensor, pullbackSimpleDegree_placed, pullbackSimpleDegree_placed,
    ← equivalenceGaugePhi_apply, ← equivalenceGaugePhi_apply] at he
  have he' : s.data.nu g h =
      t.data.nu (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h) +
        (equivalenceGaugeLambda C hC s t E h + equivalenceGaugeLambda C hC s t E (g * h) +
          equivalenceGaugeLambda C hC s t E g) := by simpa only [add_assoc] using he
  have hz := congrArg (fun x => x +
    (equivalenceGaugeLambda C hC s t E h + equivalenceGaugeLambda C hC s t E (g * h) +
      equivalenceGaugeLambda C hC s t E g)) he'
  rw [add_assoc (t.data.nu (equivalenceGaugePhi C hC s t E g)
    (equivalenceGaugePhi C hC s t E h)), CharTwo.add_self_eq_zero, add_zero] at hz
  simpa only [add_assoc] using hz.symm

end RMod.Classification
