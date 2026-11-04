import RMod.BrundanEllis.StackingReferenceShuffle
import RMod.BrundanEllis.StackingParityRedistribution

/-! The even comparison on one pair of convolution summands.  The source
contains the prescribed sum of parities plus the middle crossing; the
target has the two original parity factors on the two reordered products. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.FromRawDCT

/-- One binary summand comparison in the order used by reversedExteriorPairing. -/
def referenceBinaryBlockData (a b : ZMod 8) (X Y Z W : reference.data.Obj)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData a Y)
    (hZ : InComponent reference.data.toWeaklyPointedSuperfusionData b Z) (p q : ZMod 2) :
    IsoData reference.data.toWeaklyPointedSuperfusionData
      (reference.data.tensorObj (reference.data.tensorObj (reference.data.tensorObj X Y) (reference.data.tensorObj Z W))
        (reference.data.pi.factor (p + q + ReferenceCommutor.degree a b)))
      (reference.data.tensorObj
        (reference.data.tensorObj (reference.data.tensorObj X Z) (reference.data.pi.factor q))
        (reference.data.tensorObj (reference.data.tensorObj Y W) (reference.data.pi.factor p))) :=
  parityRedistributionData reference.data.toWeaklyPointedSuperfusionData reference.data.pi
    (reference.data.tensorObj (reference.data.tensorObj X Y) (reference.data.tensorObj Z W))
    (reference.data.tensorObj X Z) (reference.data.tensorObj Y W) p q _
    (referenceShuffleData a b X Y Z W hY hZ)

theorem referenceBinaryBlockLaws (a b : ZMod 8) (X Y Z W : reference.data.Obj)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData a Y)
    (hZ : InComponent reference.data.toWeaklyPointedSuperfusionData b Z) (p q : ZMod 2) :
    EvenIsoLaws reference.data.toWeaklyPointedSuperfusionData
      (referenceBinaryBlockData a b X Y Z W hY hZ p q) :=
  parityRedistributionLaws referenceProperty.toWeaklyPointedSuperfusionLaws referenceProperty.pi _ _ _ p q _ _
    (referenceShuffleLaws a b X Y Z W hY hZ)

/-- Odd middle crossing and two odd factors still produce an even comparison. -/
example : reference.data.IsHomogeneous 0
    (referenceBinaryBlockData 1 3 (Obj.singleton (2, 0)) (Obj.singleton (1, 1))
      (Obj.singleton (3, 0)) (Obj.singleton (4, 1))
      (referenceSingleton_component 1 1) (referenceSingleton_component 3 0) 1 1).hom :=
  (referenceBinaryBlockLaws 1 3 _ _ _ _ _ _ 1 1).hom_even

/-- A single odd target factor is also absorbed by the prescribed source parity. -/
example : reference.data.IsHomogeneous 0
    (referenceBinaryBlockData 2 4 (Obj.singleton (1, 0)) (Obj.singleton (2, 1))
      (Obj.singleton (4, 0)) (Obj.singleton (3, 1))
      (referenceSingleton_component 2 1) (referenceSingleton_component 4 0) 1 0).hom :=
  (referenceBinaryBlockLaws 2 4 _ _ _ _ _ _ 1 0).hom_even

end RMod.BrundanEllis.Stacking
