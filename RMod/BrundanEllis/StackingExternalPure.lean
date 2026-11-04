import RMod.BrundanEllis.StackingExternalPairing
import RMod.Hierarchy.Instances.GradedTensorPoints

/-! Evaluate the actual enriched exterior pairing on homogeneous pure
tensors. This records the chronological odd-odd sign at every coordinate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking
open RMod.Legacy RMod.Legacy.Hierarchy

theorem exteriorComponent_map (s t : Twist)
    (X Y : SuperTensorProduct (pullback s) (pullback t)) (g : s.group) (h : t.group) :
    (exteriorComponent s t g h).map X Y =
      ((evaluate s g).map X.1 Y.1 ⊗ₘ (evaluate t h).map X.2 Y.2) ≫
        oldTensorMap reference.toWeaklyPointedSuperfusion
          (X.1 g).val (Y.1 g).val (X.2 h).val (Y.2 h).val := by
  with_unfolding_all rfl

/-- The reference tensor at a pair of coordinates includes exactly the Koszul sign. -/
theorem exteriorPairing_tmul (s t : Twist)
    (X Y : SuperTensorProduct (pullback s) (pullback t))
    (i j a : ZMod 2) (hij : i + j = a)
    (f : SHom (pullback s) X.1 Y.1 i) (q : SHom (pullback t) X.2 Y.2 j)
    (gh : s.group × t.group) :
    ((exteriorPairing s t).map X Y a
      (ιTensorObj (SHom (pullback s) X.1 Y.1) (SHom (pullback t) X.2 Y.2)
        i j a hij (f ⊗ₜ[ℝ] q))).val gh =
      reference.data.smul ((-1 : ℝ) ^ (i * j).val)
        (reference.data.tensorHom (f.val gh.1) (q.val gh.2)) := by
  change ((exteriorComponent s t gh.1 gh.2).map X Y a _).val = _
  rw [exteriorComponent_map]
  change (oldTensorMap reference.toWeaklyPointedSuperfusion _ _ _ _ a
    ((((evaluate s gh.1).map X.1 Y.1) ⊗ₘ ((evaluate t gh.2).map X.2 Y.2)) a
      (gradedTmul _ _ i j a hij f q))).val = _
  rw [tensorHom_gradedTmul]
  exact oldTensorMap_tmul reference.toWeaklyPointedSuperfusion _ _ _ _ i j a hij
    ((evaluate s gh.1).map X.1 Y.1 i f) ((evaluate t gh.2).map X.2 Y.2 j q)

end RMod.BrundanEllis.Stacking
