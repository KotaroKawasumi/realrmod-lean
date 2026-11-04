import RMod.BrundanEllis.StackingReferenceComponentExchange
import RMod.BrundanEllis.StackingInterchangeIso

/-! The actual middle-factor interchange in the public reference category.
This is the homogeneous binary building block for the exterior tensor comparison. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.FromRawDCT

/-- Keep both directions of the actual reference exchange as isomorphism data. -/
def referenceExchangeData (a b : ZMod 8) (X Y : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y) :
    IsoData reference.data.toWeaklyPointedSuperfusionData
      (reference.data.tensorObj X Y) (reference.data.tensorObj Y X) :=
  ⟨referenceExchange a b X Y hX hY, referenceExchangeInv a b X Y hX hY⟩

theorem referenceExchangeLaws (a b : ZMod 8) (X Y : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y) :
    HomogeneousIsoLaws reference.data.toWeaklyPointedSuperfusionData (ReferenceCommutor.degree a b)
      (referenceExchangeData a b X Y hX hY) :=
  ⟨⟨(referenceExchange_inverse a b X Y hX hY).1, (referenceExchange_inverse a b X Y hX hY).2⟩,
    referenceExchange_grade a b X Y hX hY, referenceExchangeInv_grade a b X Y hX hY⟩

/-- The specified four-factor shuffle uses the given associators and reference exchange. -/
def referenceShuffleData (a b : ZMod 8) (X Y Z W : reference.data.Obj)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData a Y)
    (hZ : InComponent reference.data.toWeaklyPointedSuperfusionData b Z) :
    IsoData reference.data.toWeaklyPointedSuperfusionData
      (reference.data.tensorObj (reference.data.tensorObj X Y) (reference.data.tensorObj Z W))
      (reference.data.tensorObj (reference.data.tensorObj X Z) (reference.data.tensorObj Y W)) :=
  interchangeIsoData reference.data.toWeaklyPointedSuperfusionData X Y Z W
    (referenceExchangeData a b Y Z hY hZ)

theorem referenceShuffleLaws (a b : ZMod 8) (X Y Z W : reference.data.Obj)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData a Y)
    (hZ : InComponent reference.data.toWeaklyPointedSuperfusionData b Z) :
    HomogeneousIsoLaws reference.data.toWeaklyPointedSuperfusionData (ReferenceCommutor.degree a b)
      (referenceShuffleData a b X Y Z W hY hZ) :=
  interchangeIsoLaws referenceProperty.toWeaklyPointedSuperfusionLaws X Y Z W _ _
    (referenceExchangeLaws a b Y Z hY hZ)

/-- Exchanging type 1 and type 3 inside a four-factor tensor is odd. -/
example : reference.data.IsHomogeneous 1
    (referenceShuffleData 1 3 (Obj.singleton (2, 0)) (Obj.singleton (1, 1))
      (Obj.singleton (3, 0)) (Obj.singleton (4, 1))
      (referenceSingleton_component 1 1) (referenceSingleton_component 3 0)).hom :=
  (referenceShuffleLaws 1 3 _ _ _ _ _ _).hom_grade

/-- Exchanging type 2 and type 4 inside the same construction is even. -/
example : reference.data.IsHomogeneous 0
    (referenceShuffleData 2 4 (Obj.singleton (1, 0)) (Obj.singleton (2, 1))
      (Obj.singleton (4, 0)) (Obj.singleton (3, 1))
      (referenceSingleton_component 2 1) (referenceSingleton_component 4 0)).hom :=
  (referenceShuffleLaws 2 4 _ _ _ _ _ _).hom_grade

end RMod.BrundanEllis.Stacking
