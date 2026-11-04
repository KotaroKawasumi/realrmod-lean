import RMod.Classification.Instances.GaugeTensorComponentComparison
import RMod.Classification.Instances.EquivalenceTensorComparison
import RMod.Classification.Instances.PullbackTensorComparison
import RMod.Classification.Instances.TensorComparisonChange
import RMod.Classification.Proofs.TensorComparisonUniqueness

/-!
# The binary comparison ratio of an arbitrary model equivalence

Transport its actual inverse tensorator comparison through the three
selected homogeneous component comparisons. Both resulting comparisons
now use the same direct support-evaluation functors. Their unique real
unit ratio is retained as data. Its conversion to the manuscript's beta
must account for the specified parity normalizer and its signs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def equivalenceChangedTensorComparison (g h : s.data.group) :=
  (equivalenceTensorComparison C hC s t E
    (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h)).changeFunctors
    (equivalenceComponentComparison C hC s t E g) (equivalenceComponentComparison C hC s t E h)
    (equivalenceTensorComponentComparison C hC s t E
      (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h))

noncomputable def equivalenceGaugeRatio (g h : s.data.group) : ℝˣ :=
  Classical.choose (TensorComparison.comparison_eq_unique_unit_smul
    (S := pullbackDegreeSimple C hC s g) (T := pullbackDegreeSimple C hC s h)
    (U := pullbackReferenceSimple C hC s (pullbackDegreeSimple C hC s g))
    (V := pullbackReferenceSimple C hC s (pullbackDegreeSimple C hC s h))
    (pullbackSpanEvaluationEquivalence C hC s (pullbackDegreeSimple C hC s g))
    (pullbackSpanEvaluationEquivalence C hC s (pullbackDegreeSimple C hC s h))
    (pullbackTensorComparison C hC s (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h))
    (equivalenceChangedTensorComparison C hC s t E g h))

end RMod.Classification
