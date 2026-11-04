import RMod.Hierarchy.Instances.HomogeneousLine

/-!
# Basis and vanishing of a homogeneous line

Away from its support the line is a zero module. At its support the chosen
unit vector is a basis, using Mathlib's specified component isomorphism.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy

theorem homogeneousLine_subsingleton (a b : ZMod 2) (h : b ≠ a) :
    Subsingleton (homogeneousLine a b) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (GradedObject.isInitialSingleObjApply a (ModuleCat.of ℝ ℝ) b h).isZero

theorem homogeneousLine_smul_basis (a : ZMod 2) (f : homogeneousLine a a) :
    f = ((GradedObject.singleObjApplyIso a (ModuleCat.of ℝ ℝ)).hom f) •
      ((GradedObject.singleObjApplyIso a (ModuleCat.of ℝ ℝ)).inv 1) := by
  let e := GradedObject.singleObjApplyIso a (ModuleCat.of ℝ ℝ)
  change f = (e.hom f) • (e.inv 1)
  rw [← map_smul e.inv.hom]
  change f = e.inv (e.hom f * 1)
  rw [mul_one]
  exact (congrArg (fun m => m f) e.hom_inv_id).symm

end RMod.Legacy
