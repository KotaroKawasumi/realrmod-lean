import RMod.Classification.Instances.PullbackReferenceSimple
import RMod.Classification.Proofs.PullbackOrbitMultiplication
import RMod.Classification.Proofs.SimpleOrbitType

/-!
# Evaluation identifies the intrinsic tensor component in the reference

The support of a tensor constituent is the product of the two supports.
The given homomorphism rho converts that product into the sum of reference
types. Property P then identifies the two reference simple generators.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (S T : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem pullbackTensorReference_sameOrbit :
    SameParityOrbit C.toWeaklyPointedSuperfusionData
      (pullbackReferenceSimple C hC t
        (simpleTensorRepresentative (twistedPullback C hC t).toWeaklyPointedSuperfusion S T)).data.object
      (simpleTensorRepresentative
        ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
        (pullbackReferenceSimple C hC t S) (pullbackReferenceSimple C hC t T)).data.object := by
  let C₀ : PiSuperfusion := ⟨C, hC.toPiSuperfusionLaws⟩
  let U := pullbackReferenceSimple C hC t S
  let V := pullbackReferenceSimple C hC t T
  let R := simpleTensorRepresentative (twistedPullback C hC t).toWeaklyPointedSuperfusion S T
  let W := simpleTensorRepresentative C₀.toWeaklyPointedSuperfusion U V
  have hU : simpleType C₀ U = Multiplicative.toAdd (t.data.rho (pullbackSimpleDegree C hC t S)) :=
    HasBWType.unique C₀.toWeaklyPointedSuperfusion (simpleType_spec C₀ U)
      (pullbackReferenceSimple_type C hC t S)
  have hV : simpleType C₀ V = Multiplicative.toAdd (t.data.rho (pullbackSimpleDegree C hC t T)) :=
    HasBWType.unique C₀.toWeaklyPointedSuperfusion (simpleType_spec C₀ V)
      (pullbackReferenceSimple_type C hC t T)
  have hW : simpleType C₀ W = Multiplicative.toAdd (t.data.rho (pullbackSimpleDegree C hC t R)) := by
    dsimp only [W, R]
    rw [simpleTensorRepresentative_type, hU, hV, pullbackSimpleDegree_tensor, map_mul]
    rfl
  have htW := simpleType_spec C₀ W
  rw [hW] at htW
  exact (hC.type_detects_orbit _ _ _
    (pullbackReferenceSimple C hC t R).laws.simple W.laws.simple
    (pullbackReferenceSimple_type C hC t R)).mp htW

end RMod.Classification
