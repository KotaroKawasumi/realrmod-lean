import RMod.Classification.Proofs.PullbackUnitLabel

/-! # The image support of every simple is computed by the induced group map -/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem equivalenceSimpleDegree (S : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion) :
    pullbackSimpleDegree C hC t (E.mapSimple S) =
      equivalenceGaugePhi C hC s t E (pullbackSimpleDegree C hC s S) := by
  let q := simpleOrbitMk (twistedPullback C hC s).toWeaklyPointedSuperfusion S
  exact congrArg (fun x => pullbackOrbitMulEquiv C hC t (E.simpleOrbitMulEquiv x))
    ((pullbackOrbitMulEquiv C hC s).symm_apply_apply q).symm

theorem equivalenceTensorRightDegree_eq
    (S T : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion) :
    (pullbackSimpleDegree C hC t (E.mapSimple S))⁻¹ *
      pullbackSimpleDegree C hC t
        (E.mapSimple (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T)) =
      pullbackSimpleDegree C hC t (E.mapSimple T) := by
  rw [equivalenceSimpleDegree, equivalenceSimpleDegree, equivalenceSimpleDegree,
    pullbackSimpleDegree_tensor, map_mul, inv_mul_cancel_left]

end RMod.Classification
