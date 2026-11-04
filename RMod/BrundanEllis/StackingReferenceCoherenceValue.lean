import RMod.BrundanEllis.StackingReferenceValue
import RMod.Hierarchy.Bridge.MonoidalLaws

/-! The public reference coherence maps retain the concrete executable
associator and unitors through the interface roundtrip. In particular,
the actual associator includes its original endpoint parity normalization. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Legacy.Hierarchy Superfusion.RMod.FromRawDCT

/-- The public associator reads back to the endpoint-normalized raw associator. -/
theorem referenceValue_associator (X Y Z : reference.data.Obj) :
    referenceValue (reference.data.associatorHom X Y Z) = RealAssociator.hom X Y Z := by
  have h := (totalHomEquiv_even RMod.realRModLegacy _ _
    ((ofOldMonoidalStructureData RMod.realRModLegacy).associatorHom X Y Z)).trans
      (oldEven_associatorHom_value RMod.realRModLegacy X Y Z)
  with_unfolding_all exact h

/-- The reverse public associator reads back to the specified raw inverse. -/
theorem referenceValue_associatorInv (X Y Z : reference.data.Obj) :
    referenceValue (reference.data.associatorInv X Y Z) = RealAssociator.inv X Y Z := by
  have h := (totalHomEquiv_even RMod.realRModLegacy _ _
    ((ofOldMonoidalStructureData RMod.realRModLegacy).associatorInv X Y Z)).trans
      (oldEven_associatorInv_value RMod.realRModLegacy X Y Z)
  with_unfolding_all exact h

/-- The left unit comparison is retained by the same roundtrip. -/
theorem referenceValue_leftUnitor (X : reference.data.Obj) :
    referenceValue (reference.data.leftUnitorHom X) = RMod.realRModData.leftUnitorHom X := by
  have h := (totalHomEquiv_even RMod.realRModLegacy _ _
    ((ofOldMonoidalStructureData RMod.realRModLegacy).leftHom X)).trans
      (oldEven_leftHom_value RMod.realRModLegacy X)
  with_unfolding_all exact h

/-- The right unit comparison is retained by the same roundtrip. -/
theorem referenceValue_rightUnitor (X : reference.data.Obj) :
    referenceValue (reference.data.rightUnitorHom X) = RMod.realRModData.rightUnitorHom X := by
  have h := (totalHomEquiv_even RMod.realRModLegacy _ _
    ((ofOldMonoidalStructureData RMod.realRModLegacy).rightHom X)).trans
      (oldEven_rightHom_value RMod.realRModLegacy X)
  with_unfolding_all exact h

end RMod.BrundanEllis.Stacking
