import RMod.Classification.Instances.EquivalenceTensorEvaluation
import RMod.Classification.Instances.ConvolutionComponentReindex
import RMod.Classification.Abstract.TensorComparison
import RMod.Classification.Proofs.EquivalenceSupportMultiplication

/-!
# The binary comparison induced by the given monoidal tensorator

Evaluate the inverse tensorator at the image product support, project to
the surviving target summand, and delete its right parity factor. The
forward tensorator supplies the first specified inverse map.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def equivalenceTensoratorComponentData (X Y : PullbackObj C s.data) (k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (E.data.forward.obj ((twistedPullback C hC s).data.tensorObj X Y) k).val
      (convolutionObj C hC t.data (E.data.forward.obj X) (E.data.forward.obj Y) k).val :=
  ⟨E.data.forward.tensorInv X Y k, E.data.forward.tensorHom X Y k⟩

noncomputable def equivalenceTensorComparisonData
    (S T : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion) :
    TensorComparisonData S T (pullbackReferenceSimple C hC s S) (pullbackReferenceSimple C hC s T)
      (equivalenceEvaluatedComponent C hC s t E S).forwardFunctor.data
      (equivalenceEvaluatedComponent C hC s t E T).forwardFunctor.data
      (equivalenceTensorEvaluation C hC s t E S T).forwardFunctor.data where
  app X Y :=
    let k := pullbackSimpleDegree C hC t (E.mapSimple
      (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T))
    (equivalenceTensoratorComponentData C hC s t E X.obj Y.obj k).trans C.toWeaklyPointedSuperfusionData
      (convolutionComponentReindexData C hC t.data (E.data.forward.obj X.obj) (E.data.forward.obj Y.obj)
        k (pullbackSimpleDegree C hC t (E.mapSimple S)) (pullbackSimpleDegree C hC t (E.mapSimple T))
        (equivalenceTensorRightDegree_eq C hC s t E S T))

end RMod.Classification
