import RMod.Classification.Instances.PullbackTensorEvaluation
import RMod.Classification.Instances.ConvolutionComponentReindex
import RMod.Classification.Abstract.TensorComparison

/-!
# The binary comparison carried by direct support evaluation

Its maps are the actual convolution projection and inclusion, the right
factor deletion and insertion, and the forced complementary-index map.
Thus its parity measures the given cochain nu of the model itself.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (S T : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem pullbackTensorRightDegree_eq :
    (pullbackSimpleDegree C hC t S)⁻¹ *
      pullbackSimpleDegree C hC t
        (simpleTensorRepresentative (twistedPullback C hC t).toWeaklyPointedSuperfusion S T) =
      pullbackSimpleDegree C hC t T := by
  rw [pullbackSimpleDegree_tensor, inv_mul_cancel_left]

noncomputable def pullbackTensorComparisonData :
    TensorComparisonData S T (pullbackReferenceSimple C hC t S) (pullbackReferenceSimple C hC t T)
      (pullbackSpanEvaluationEquivalence C hC t S).forwardFunctor.data
      (pullbackSpanEvaluationEquivalence C hC t T).forwardFunctor.data
      (pullbackTensorEvaluation C hC t S T).forwardFunctor.data where
  app X Y := convolutionComponentReindexData C hC t.data X.obj Y.obj
    (pullbackSimpleDegree C hC t
      (simpleTensorRepresentative (twistedPullback C hC t).toWeaklyPointedSuperfusion S T))
    (pullbackSimpleDegree C hC t S) (pullbackSimpleDegree C hC t T)
    (pullbackTensorRightDegree_eq C hC t S T)

end RMod.Classification
