import RMod.BrundanEllis.StackingExternalReversed
import RMod.BrundanEllis.StackingExternalPure

/-! The two Koszul signs in the reversed exterior pairing cancel. This is
its formula on actual homogeneous generators of the enriched tensor Hom. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking
open RMod.Legacy

/-- Reversing the inputs cancels the chronological tensor convention sign. -/
theorem reversedExteriorPairing_tmul (s t : Twist)
    (X Y : SuperTensorProduct (pullback s) (pullback t))
    (i j a : ZMod 2) (hij : i + j = a)
    (f : SHom (pullback s) X.1 Y.1 i) (q : SHom (pullback t) X.2 Y.2 j)
    (gh : s.group × t.group) :
    ((reversedExteriorPairing s t).map X Y a
      (gradedTmul (SHom (pullback s) X.1 Y.1) (SHom (pullback t) X.2 Y.2)
        i j a hij f q)).val gh =
      reference.data.tensorHom (q.val gh.2) (f.val gh.1) := by
  change ((exteriorPairing t s).map (X.2, X.1) (Y.2, Y.1) a
    (koszulMap (SHom (pullback s) X.1 Y.1) (SHom (pullback t) X.2 Y.2) a
      (gradedTmul _ _ i j a hij f q))).val (gh.2, gh.1) = _
  erw [koszulMap_gradedTmul, map_smul]
  change reference.data.smul ((-1 : ℝ) ^ (i * j).val)
    (((exteriorPairing t s).map (X.2, X.1) (Y.2, Y.1) a
      (gradedTmul _ _ j i a (by rw [add_comm, hij]) q f)).val (gh.2, gh.1)) = _
  erw [exteriorPairing_tmul, mul_comm j i,
    ← referenceProperty.toWeaklyPointedSuperfusionLaws.mul_smul]
  rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  exact referenceProperty.toWeaklyPointedSuperfusionLaws.one_smul _

set_option maxHeartbeats 1000000 in
/-- The formula also holds as an equality of the whole coordinate family. -/
theorem reversedExteriorPairing_value (s t : Twist)
    (X Y : SuperTensorProduct (pullback s) (pullback t))
    (i j a : ZMod 2) (hij : i + j = a)
    (f : SHom (pullback s) X.1 Y.1 i) (q : SHom (pullback t) X.2 Y.2 j) :
    ((reversedExteriorPairing s t).map X Y a
      (gradedTmul (SHom (pullback s) X.1 Y.1) (SHom (pullback t) X.2 Y.2)
        i j a hij f q)).val =
      (fun gh : s.group × t.group => reference.data.tensorHom (q.val gh.2) (f.val gh.1)) := by
  funext gh
  exact reversedExteriorPairing_tmul s t X Y i j a hij f q gh

end RMod.BrundanEllis.Stacking
