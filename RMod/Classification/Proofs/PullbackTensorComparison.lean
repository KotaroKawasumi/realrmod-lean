import RMod.Classification.Instances.PullbackTensorComparisonData
import RMod.Classification.Proofs.ConvolutionComponentReindex

/-!
# Direct evaluation has exactly the model's binary comparison parity

Objects in a simple span have that simple's support. The actual binary
comparison is consequently invertible and has degree nu(g,h). Its signed
naturality is the already proved convolution component square.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (S T : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem pullbackTensorComparison_homogeneousIso
    (X : HomogeneousSpanCategory (twistedPullback C hC t).toWeaklyPointedSuperfusion S.data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC t).toWeaklyPointedSuperfusion T.data.object) :
    HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData
      (t.data.nu (pullbackSimpleDegree C hC t S) (pullbackSimpleDegree C hC t T))
      ((pullbackTensorComparisonData C hC t S T).app X Y) :=
  convolutionComponentReindex_homogeneousIso C hC t.data X.obj Y.obj _ _ _
    (pullbackTensorRightDegree_eq C hC t S T) (pullback_span_supported C hC t S X)

theorem pullbackTensorComparisonLaws :
    TensorComparisonLaws S T (pullbackReferenceSimple C hC t S) (pullbackReferenceSimple C hC t T)
      (t.data.nu (pullbackSimpleDegree C hC t S) (pullbackSimpleDegree C hC t T))
      (pullbackTensorComparisonData C hC t S T) where
  iso X Y := (pullbackTensorComparison_homogeneousIso C hC t S T X Y).toIsoLaws
  hom_grade X Y := (pullbackTensorComparison_homogeneousIso C hC t S T X Y).hom_grade
  inv_grade X Y := (pullbackTensorComparison_homogeneousIso C hC t S T X Y).inv_grade
  naturality f q hf hq := convolutionComponentReindex_naturality C hC t.data f.hom q.hom hf hq _ _ _
    (pullbackTensorRightDegree_eq C hC t S T)

end RMod.Classification
