import RMod.Statement.FusionBridge

/-!
# Preservation of the reference property

The parity orbits and graded endomorphism algebras are unchanged. Thus the
eight Brauer-Wall types retain the same witnesses in either presentation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace RMod.StatementLegacy.StatementBridge

theorem hasType_fromFusion (C : Legacy.FusionPiSupercategory)
    (X : Legacy.Even C.toMonoidalPiSupercategory.monoidal.super) (r : ZMod 8) :
    HasBrauerWallType (fromFusion C) X r ↔ Legacy.HasBrauerWallType C X r := by
  simp only [HasBrauerWallType, Legacy.HasBrauerWallType, orbit_fromSuper, grade_mem_iff]
  rfl

theorem hasType_toFusion (C : FusionPiSupercategory)
    (X : Even C.toMonoidalPiSupercategory.monoidal.super) (r : ZMod 8) :
    Legacy.HasBrauerWallType (toFusion C) X r ↔ HasBrauerWallType C X r := by
  simp only [HasBrauerWallType, Legacy.HasBrauerWallType, orbit_toSuper, grade_mem_iff]
  rfl

theorem fromReference (C : Legacy.WeaklyPointedFusionPiSupercategory)
    (h : Legacy.IsBrauerWallReference C) : IsBrauerWallReference (fromWeak C) where
  simple_type X hX := by
    obtain ⟨r, hr, hu⟩ := h.simple_type X hX
    exact ⟨r, (hasType_fromFusion _ _ _).mpr hr,
      fun s hs => hu s ((hasType_fromFusion _ _ _).mp hs)⟩
  realizes_type r := by
    obtain ⟨X, hX, htype⟩ := h.realizes_type r
    exact ⟨X, hX, (hasType_fromFusion _ _ _).mpr htype⟩
  type_detects_orbit X Y r hX hY htype :=
    (hasType_fromFusion _ _ _).trans
      ((h.type_detects_orbit X Y r hX hY ((hasType_fromFusion _ _ _).mp htype)).trans
        (orbit_fromSuper _ _ _).symm)

theorem toReference (C : WeaklyPointedFusionPiSupercategory)
    (h : IsBrauerWallReference C) : Legacy.IsBrauerWallReference (toWeak C) where
  simple_type X hX := by
    obtain ⟨r, hr, hu⟩ := h.simple_type X hX
    exact ⟨r, (hasType_toFusion _ _ _).mpr hr,
      fun s hs => hu s ((hasType_toFusion _ _ _).mp hs)⟩
  realizes_type r := by
    obtain ⟨X, hX, htype⟩ := h.realizes_type r
    exact ⟨X, hX, (hasType_toFusion _ _ _).mpr htype⟩
  type_detects_orbit X Y r hX hY htype :=
    (hasType_toFusion _ _ _).trans
      ((h.type_detects_orbit X Y r hX hY ((hasType_toFusion _ _ _).mp htype)).trans
        (orbit_toSuper _ _ _).symm)

/-- The old presentation is recovered with the original data and proof fields. -/
theorem toWeak_fromWeak (C : Legacy.WeaklyPointedFusionPiSupercategory) :
    toWeak (fromWeak C) = C := by
  cases C
  rfl

end RMod.StatementLegacy.StatementBridge
