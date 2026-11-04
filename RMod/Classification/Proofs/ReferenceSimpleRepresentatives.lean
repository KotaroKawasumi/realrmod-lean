import RMod.Classification.Instances.ReferenceSimpleRepresentatives

/-!
# Tensor products of the reference's chosen type representatives

The intrinsic type of a tensor constituent is the sum of the two types.
The reference property then identifies its parity orbit with the chosen
representative of that sum. No concrete model of the reference is used.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem referenceSimpleRepresentative_simpleType (r : ZMod 8) :
    simpleType C (referenceSimpleRepresentative C hC r) = r :=
  HasBWType.unique C.toWeaklyPointedSuperfusion
    (simpleType_spec C _) (referenceSimpleRepresentative_type C hC r)

theorem referenceSimpleRepresentative_mul (r s : ZMod 8) :
    SameParityOrbit C.data.toWeaklyPointedSuperfusionData
      (simpleTensorRepresentative C.toWeaklyPointedSuperfusion
        (referenceSimpleRepresentative C hC r) (referenceSimpleRepresentative C hC s)).data.object
      (referenceSimpleRepresentative C hC (r + s)).data.object := by
  let X := simpleTensorRepresentative C.toWeaklyPointedSuperfusion
    (referenceSimpleRepresentative C hC r) (referenceSimpleRepresentative C hC s)
  have htype : HasBWType C.data.toWeaklyPointedSuperfusionData X.data.object (r + s) := by
    have h := simpleType_spec C X
    have he := simpleTensorRepresentative_type C
      (referenceSimpleRepresentative C hC r) (referenceSimpleRepresentative C hC s)
    rw [referenceSimpleRepresentative_simpleType, referenceSimpleRepresentative_simpleType] at he
    change simpleType C X = r + s at he
    rw [he] at h
    exact h
  exact (hC.type_detects_orbit _ _ (r + s) X.laws.simple
    (referenceSimpleRepresentative C hC (r + s)).laws.simple htype).mp
    (referenceSimpleRepresentative_type C hC (r + s))

end RMod.Classification
