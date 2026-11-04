import RMod.BrundanEllis.StackingSuperInterchangeUnit
import RMod.BrundanEllis.StackingReferenceShuffleAssociativity
import RMod.BrundanEllis.StackingReferenceUnitExchange

/-! Both unit identities for the actual reference shuffle, using the previously verified reference exchanges with the unit. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => WeaklyPointedSuperfusion.mk reference.data.toWeaklyPointedSuperfusionData
  referenceProperty.toWeaklyPointedSuperfusionLaws

/-- The actual reference shuffle respects the left unit comparison. -/
theorem referenceShuffle_leftUnit (a : ZMod 8) (X Y : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X) :
    reference.data.comp
      (referenceShuffleData 0 a reference.data.tensorUnit reference.data.tensorUnit X Y
        (InComponent.tensor_unit referenceProperty) hX).hom
      (reference.data.tensorHom (reference.data.leftUnitorHom X) (reference.data.leftUnitorHom Y)) =
    reference.data.comp
      (reference.data.tensorHom (reference.data.leftUnitorHom reference.data.tensorUnit)
        (reference.data.id (reference.data.tensorObj X Y)))
      (reference.data.leftUnitorHom (reference.data.tensorObj X Y)) := by
  rw [referenceShuffle_hom]
  exact superInterchange_leftUnit R X Y _
    (referenceExchange_even 0 a (by simp [ReferenceCommutor.degree])
      _ X (InComponent.tensor_unit referenceProperty) hX).hom_even
    (referenceExchange_leftUnit a X hX)

/-- The actual reference shuffle respects the right unit comparison. -/
theorem referenceShuffle_rightUnit (a : ZMod 8) (X Y : reference.data.Obj)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData a Y) :
    reference.data.comp
      (referenceShuffleData a 0 X Y reference.data.tensorUnit reference.data.tensorUnit
        hY (InComponent.tensor_unit referenceProperty)).hom
      (reference.data.tensorHom (reference.data.rightUnitorHom X) (reference.data.rightUnitorHom Y)) =
    reference.data.comp
      (reference.data.tensorHom (reference.data.id (reference.data.tensorObj X Y))
        (reference.data.leftUnitorHom reference.data.tensorUnit))
      (reference.data.rightUnitorHom (reference.data.tensorObj X Y)) := by
  rw [referenceShuffle_hom]
  exact superInterchange_rightUnit R X Y _
    (referenceExchange_even a 0 (by simp [ReferenceCommutor.degree])
      Y _ hY (InComponent.tensor_unit referenceProperty)).hom_even
    (referenceExchange_rightUnit a Y hY)

end RMod.BrundanEllis.Stacking
