import RMod.Hierarchy.Bridge.LegacyCoherence

/-! Mathlib's chosen right and left duals supply the legacy existential laws. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy

theorem legacyRightDual (A : FusionPiSupercategory)
    (X : (toOldData A.toMonoidalPiSupercategory.monoidal).Obj) :
    ∃ Y, (toOldData A.toMonoidalPiSupercategory.monoidal).HasExactPairing X Y := by
  obtain ⟨h⟩ := A.rigid
  letI : RigidCategory (Even A.toMonoidalPiSupercategory.monoidal.super) := h
  let X' : Even A.toMonoidalPiSupercategory.monoidal.super := evenObj A.toMonoidalPiSupercategory.monoidal.super X
  exact ⟨HasRightDual.rightDual (C := Even A.toMonoidalPiSupercategory.monoidal.super) X',
    legacyExactPairing A.toMonoidalPiSupercategory.monoidal X' (HasRightDual.rightDual (C := Even A.toMonoidalPiSupercategory.monoidal.super) X')⟩

theorem legacyLeftDual (A : FusionPiSupercategory)
    (X : (toOldData A.toMonoidalPiSupercategory.monoidal).Obj) :
    ∃ Y, (toOldData A.toMonoidalPiSupercategory.monoidal).HasExactPairing Y X := by
  obtain ⟨h⟩ := A.rigid
  letI : RigidCategory (Even A.toMonoidalPiSupercategory.monoidal.super) := h
  let X' : Even A.toMonoidalPiSupercategory.monoidal.super := evenObj A.toMonoidalPiSupercategory.monoidal.super X
  exact ⟨HasLeftDual.leftDual (C := Even A.toMonoidalPiSupercategory.monoidal.super) X',
    legacyExactPairing A.toMonoidalPiSupercategory.monoidal (HasLeftDual.leftDual (C := Even A.toMonoidalPiSupercategory.monoidal.super) X') X'⟩

end RMod.Legacy.Hierarchy
