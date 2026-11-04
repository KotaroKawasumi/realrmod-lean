import RMod.Classification.Instances.PullbackSimpleLabels

/-! # The actual reference simple obtained by evaluating a model simple -/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (S : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def pullbackReferenceSimpleData : SimpleObjectData C.toWeaklyPointedSuperfusionData :=
  ⟨(S.data.object (pullbackSimpleDegree C hC t S)).val⟩

theorem pullbackReferenceSimpleLaws :
    SimpleObjectLaws C.toWeaklyPointedSuperfusionData (pullbackReferenceSimpleData C hC t S) :=
  ⟨pullbackSimpleDegree_simple C hC t S⟩

noncomputable def pullbackReferenceSimple :
    SimpleObject ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ :=
  ⟨pullbackReferenceSimpleData C hC t S, pullbackReferenceSimpleLaws C hC t S⟩

theorem pullbackReferenceSimple_type :
    HasBWType C.toWeaklyPointedSuperfusionData (pullbackReferenceSimple C hC t S).data.object
      (Multiplicative.toAdd (t.data.rho (pullbackSimpleDegree C hC t S))) :=
  (InComponent.simple_iff hC (pullbackSimpleDegree_simple C hC t S) _).mp
    (S.data.object (pullbackSimpleDegree C hC t S)).property

end RMod.Classification
