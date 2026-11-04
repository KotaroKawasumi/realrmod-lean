import RMod.Classification.Instances.SimpleOrbitRepresentatives
import RMod.Classification.Instances.ReferenceGrading

/-!
# Reference representatives selected by intrinsic type

Use the inverse of the reference's proved type isomorphism to select a
simple in each type. The identity-class convention chooses the actual
tensor unit in type zero. Object data and simplicity laws are separate.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def referenceSimpleRepresentativeData (r : ZMod 8) :
    SimpleObjectData C.data.toWeaklyPointedSuperfusionData :=
  simpleOrbitRepresentativeData C.toWeaklyPointedSuperfusion
    ((referenceGradingEquiv C hC).symm (Multiplicative.ofAdd r))

theorem referenceSimpleRepresentativeLaws (r : ZMod 8) :
    SimpleObjectLaws C.data.toWeaklyPointedSuperfusionData (referenceSimpleRepresentativeData C hC r) :=
  simpleOrbitRepresentativeLaws C.toWeaklyPointedSuperfusion _

noncomputable def referenceSimpleRepresentative (r : ZMod 8) : SimpleObject C.toWeaklyPointedSuperfusion :=
  ⟨referenceSimpleRepresentativeData C hC r, referenceSimpleRepresentativeLaws C hC r⟩

theorem referenceSimpleRepresentative_zero :
    referenceSimpleRepresentative C hC 0 = unitSimple C.toWeaklyPointedSuperfusion := by
  change simpleOrbitRepresentative C.toWeaklyPointedSuperfusion
    ((referenceGradingEquiv C hC).symm 1) = _
  rw [map_one]
  exact simpleOrbitRepresentative_one C.toWeaklyPointedSuperfusion

theorem referenceSimpleRepresentative_type (r : ZMod 8) :
    HasBWType C.data.toWeaklyPointedSuperfusionData (referenceSimpleRepresentative C hC r).data.object r := by
  have h : (intrinsicRho C)
      (simpleOrbitMk C.toWeaklyPointedSuperfusion (referenceSimpleRepresentative C hC r)) =
        Multiplicative.ofAdd r := by
    change referenceGradingEquiv C hC (simpleOrbitMk C.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative C.toWeaklyPointedSuperfusion
        ((referenceGradingEquiv C hC).symm (Multiplicative.ofAdd r)))) = _
    rw [simpleOrbitRepresentative_class, MulEquiv.apply_symm_apply]
  have he : simpleType C (referenceSimpleRepresentative C hC r) = r :=
    congrArg Multiplicative.toAdd h
  have hs := simpleType_spec C (referenceSimpleRepresentative C hC r)
  rw [he] at hs
  exact hs

end RMod.Classification
