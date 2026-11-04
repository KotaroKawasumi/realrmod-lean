import RMod.BrundanEllis.ParityComparisons

/-! Inverse odd naturality follows from the already proved inverse equations.
This argument uses only associative total composition and scalar linearity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace RMod.Legacy.BrundanEllisParity
open RMod.Legacy.Hierarchy
-- These local unfolding hints affect elaboration only; the kernel still checks every proof.
set_option allowUnsafeReducibility true
attribute [local reducible] RMod.Legacy.MonoidalSupercategory.super
  RMod.Legacy.Hierarchy.toOldData RMod.Classification.PiData.shiftObj
  RMod.Classification.PiData.shiftHom RMod.Classification.PiData.zHom
  RMod.Classification.PiData.zInv RMod.Legacy.TotalCategory
  RMod.Legacy.superTensorProductData

variable (C : RMod.Legacy.MonoidalSupercategory)
  (p : RMod.Classification.Pi (toOldData C))

theorem z_inv_naturality {X Y : C.data.Obj} (a : ZMod 2)
    (f : THom C.super.data X Y) (hf : f ∈ grade C.super X Y a) :
    tComp C.super.data (p.data.zInv X) (p.data.shiftHom f) =
      (-1 : ℝ) ^ a.val • tComp C.super.data f (p.data.zInv Y) := by
  calc
    _ = tComp C.super.data
        (tComp C.super.data (p.data.zInv X)
          (tComp C.super.data (p.data.shiftHom f) (p.data.zHom Y))) (p.data.zInv Y) := by
      rw [tComp_assoc C.super, tComp_assoc C.super, z_hom_inv C p Y, tComp_id_right]
    _ = _ := by
      rw [z_naturality C p a f hf, tComp_smul_right, tComp_smul_left,
        ← tComp_assoc C.super, z_inv_hom C p X, tComp_id_left]

end RMod.Legacy.BrundanEllisParity
