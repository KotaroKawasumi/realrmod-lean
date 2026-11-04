import RMod.Classification.Instances.PullbackOrbitLabels
import RMod.Classification.Instances.SimpleOrbitGroup
import RMod.Classification.Proofs.ConvolutionSupport

/-!
# Tensor products multiply the intrinsic support labels

A simple tensor constituent retracts from the actual convolution tensor.
Its nonzero coordinate cannot lie outside the product of the two supports,
since convolution has zero identity at every other coordinate.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)

theorem pullbackSimpleDegree_tensor
    (X Y : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    pullbackSimpleDegree C hC t
        (simpleTensorRepresentative (twistedPullback C hC t).toWeaklyPointedSuperfusion X Y) =
      pullbackSimpleDegree C hC t X * pullbackSimpleDegree C hC t Y := by
  let D := (twistedPullback C hC t).toWeaklyPointedSuperfusion
  let S := simpleTensorRepresentative D X Y
  let d := simpleDecomposition D (D.data.tensorObj X.data.object Y.data.object)
  let i := tensorSimpleIndex D X Y
  let k := pullbackSimpleDegree C hC t S
  by_contra he
  have hz := convolution_support C hC t.data
    (pullbackSimpleDegree C hC t X) (pullbackSimpleDegree C hC t Y)
    (pullbackSimpleDegree_supported C hC t X) (pullbackSimpleDegree_supported C hC t Y) k he
  have hj := hom_eq_zero_of_target hC.toWeaklyPointedSuperfusionLaws hz
    (d.data.decomposition.inclusion i k)
  have hd : C.comp (d.data.decomposition.inclusion i k) (d.data.decomposition.projection i k) =
      C.id (S.data.object k).val := congrFun (d.laws.decomposition.diagonal i) k
  rw [hj] at hd
  exact simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws
    (pullbackSimpleDegree_simple C hC t S)
    (hd.symm.trans (raw_zero_comp hC.toWeaklyPointedSuperfusionLaws _))

theorem pullbackOrbitDegree_mul
    (g h : SimpleOrbit (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    pullbackOrbitDegree C hC t (g * h) = pullbackOrbitDegree C hC t g * pullbackOrbitDegree C hC t h := by
  refine Quotient.inductionOn₂ g h ?_
  exact pullbackSimpleDegree_tensor C hC t

end RMod.Classification
