import RMod.Definitions.WeaklyPointedSuperfusion

/-!
# Explicit dual-pairing and dual-choice data

The coevaluation and evaluation are computational maps. Their evenness
and the two snake identities belong to laws on these precise maps. A
choice of left and right duals retains both objects and both pairing data;
its laws only verify the chosen pairings.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

structure DualPairingData (C : WeaklyPointedSuperfusionData.{u, v}) (X Y : C.Obj) where
  coeval : C.Hom C.tensorUnit (C.tensorObj X Y)
  eval : C.Hom (C.tensorObj Y X) C.tensorUnit

structure DualPairingLaws (C : WeaklyPointedSuperfusionData.{u, v})
    {X Y : C.Obj} (d : DualPairingData C X Y) : Prop where
  coeval_even : C.IsHomogeneous 0 d.coeval
  eval_even : C.IsHomogeneous 0 d.eval
  snake_right :
    C.comp (C.comp (C.whiskerLeft Y d.coeval) (C.associatorInv Y X Y))
        (C.whiskerRight d.eval Y) =
      C.comp (C.rightUnitorHom Y) (C.leftUnitorInv Y)
  snake_left :
    C.comp (C.comp (C.whiskerRight d.coeval X) (C.associatorHom X Y X))
        (C.whiskerLeft X d.eval) =
      C.comp (C.leftUnitorHom X) (C.rightUnitorInv X)

structure DualPairing (C : WeaklyPointedSuperfusion.{u, v}) (X Y : C.data.Obj) where
  data : DualPairingData C.data X Y
  laws : DualPairingLaws C.data data

structure DualChoicesData (C : WeaklyPointedSuperfusionData.{u, v}) where
  rightObj : C.Obj → C.Obj
  leftObj : C.Obj → C.Obj
  rightPairing : (X : C.Obj) → DualPairingData C X (rightObj X)
  leftPairing : (X : C.Obj) → DualPairingData C (leftObj X) X

structure DualChoicesLaws (C : WeaklyPointedSuperfusionData.{u, v})
    (d : DualChoicesData C) : Prop where
  rightPairing : ∀ X, DualPairingLaws C (d.rightPairing X)
  leftPairing : ∀ X, DualPairingLaws C (d.leftPairing X)

structure DualChoices (C : WeaklyPointedSuperfusion.{u, v}) where
  data : DualChoicesData C.data
  laws : DualChoicesLaws C.data data

end RMod.Classification
