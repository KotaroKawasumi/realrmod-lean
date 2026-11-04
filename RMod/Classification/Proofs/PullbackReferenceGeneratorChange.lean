import RMod.Classification.Instances.PullbackReferenceSimple
import RMod.Classification.Proofs.PullbackSimpleLabels

/-! # Equal supports give the same reference simple component -/

set_option autoImplicit false

namespace RMod.Classification

theorem pullbackReference_sameOrbit_of_degree_eq
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
    (S T : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (e : pullbackSimpleDegree C hC t S = pullbackSimpleDegree C hC t T) :
    SameParityOrbit C.toWeaklyPointedSuperfusionData
      (pullbackReferenceSimple C hC t S).data.object (pullbackReferenceSimple C hC t T).data.object := by
  have hT := pullbackReferenceSimple_type C hC t T
  have hT' := Eq.mp (congrArg (fun r => HasBWType C.toWeaklyPointedSuperfusionData
    (pullbackReferenceSimple C hC t T).data.object r)
    (congrArg (fun g => Multiplicative.toAdd (t.data.rho g)) e.symm)) hT
  exact (hC.type_detects_orbit _ _ _ (pullbackReferenceSimple C hC t S).laws.simple
    (pullbackReferenceSimple C hC t T).laws.simple (pullbackReferenceSimple_type C hC t S)).mp hT'

end RMod.Classification
