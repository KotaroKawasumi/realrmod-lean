import RMod.BrundanEllis.StackingHullSupport
import RMod.BrundanEllis.StackingHullFusion

/-! Dual closure follows from the finite intrinsic orbit group. On simples,
a dual pairing gives inverse parity classes. For arbitrary objects, dualizing
a split inclusion reduces the question to those simple classes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable (C : WeaklyPointedFusionPiSuperCat)

/-- The existing bridge sends an actual even exact pairing to the raw laws. -/
theorem intrinsic_pairing (X Y : Even C) [ExactPairing X Y] :
    (intrinsicOld C).data.HasExactPairing X Y := by
  let M := (RMod.EnrichedBridge.toWeak (Bridge.toStage C)).toMonoidalPiSupercategory.monoidal
  let L := RMod.StatementLegacy.StatementBridge.toMonoidal M
  letI : @ExactPairing (RMod.Legacy.Even L.super) _
      (RMod.Legacy.evenCategoryMonoidal L) X Y := by
    change @ExactPairing (Even C) _
      (RMod.Legacy.evenCategoryMonoidal (RMod.StatementLegacy.StatementBridge.toMonoidal M)) X Y
    rw [RMod.StatementLegacy.StatementBridge.toMonoidal_even]
    exact (inferInstance : ExactPairing X Y)
  with_unfolding_all
    exact RMod.Legacy.Hierarchy.legacyExactPairing L X Y

/-- The ordinary dual of a simple object remains simple. -/
theorem pairing_right_simple (X Y : Even C) [ExactPairing X Y] [Simple X] : Simple Y := by
  obtain ⟨p⟩ := (RMod.Classification.hasExactPairing_iff
    (intrinsicOld C).toWeaklyPointedSuperfusion X Y).mp (intrinsic_pairing C X Y)
  exact (intrinsic_simple C Y).mp (p.right_simple ((intrinsic_simple C X).mpr (inferInstance : Simple X)))

theorem pairing_left_simple (X Y : Even C) [ExactPairing X Y] [Simple Y] : Simple X := by
  obtain ⟨p⟩ := (RMod.Classification.hasExactPairing_iff
    (intrinsicOld C).toWeaklyPointedSuperfusion X Y).mp (intrinsic_pairing C X Y)
  exact (intrinsic_simple C X).mp (p.left_simple ((intrinsic_simple C Y).mpr (inferInstance : Simple Y)))

variable {I : Type} (Z : I → Even C) [ObjectProperty.IsMonoidal (AddPiHull C Z)]

theorem pairing_right_mem (X Y : Even C) [ExactPairing X Y] [Simple X]
    (hX : AddPiHull C Z X) : AddPiHull C Z Y := by
  obtain ⟨p⟩ := (RMod.Classification.hasExactPairing_iff
    (intrinsicOld C).toWeaklyPointedSuperfusion X Y).mp (intrinsic_pairing C X Y)
  let S : RMod.Classification.SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion :=
    ⟨⟨X⟩, ⟨(intrinsic_simple C X).mpr (inferInstance : Simple X)⟩⟩
  let T : RMod.Classification.SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion :=
    ⟨⟨Y⟩, ⟨p.right_simple S.laws.simple⟩⟩
  exact simple_pairing_right_mem C Z S T p hX

theorem pairing_left_mem (X Y : Even C) [ExactPairing X Y] [Simple Y]
    (hY : AddPiHull C Z Y) : AddPiHull C Z X := by
  obtain ⟨p⟩ := (RMod.Classification.hasExactPairing_iff
    (intrinsicOld C).toWeaklyPointedSuperfusion X Y).mp (intrinsic_pairing C X Y)
  let T : RMod.Classification.SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion :=
    ⟨⟨Y⟩, ⟨(intrinsic_simple C Y).mpr (inferInstance : Simple Y)⟩⟩
  let S : RMod.Classification.SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion :=
    ⟨⟨X⟩, ⟨p.left_simple T.laws.simple⟩⟩
  exact simple_pairing_left_mem C Z S T p hY

end Stacking
end RMod.BrundanEllis
