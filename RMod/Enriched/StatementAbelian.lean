import RMod.Enriched.SplitAbelian
import RMod.Statement.FusionBridge
import RMod.Hierarchy.Instances.EvenTotal

/-! The previously proved models are abelian: finite semisimple decompositions
and the existing homogeneous Schur theorem split every matrix into its image,
kernel, and cokernel. This is a construction, not an additional model axiom. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace RMod.EnrichedBridge

/-- The existing graded Schur proof gives ordinary Schur through the faithful even inclusion. -/
theorem statementEvenSchur (C : StatementLegacy.FusionPiSupercategory)
    (X Y : StatementLegacy.Even C.toSupercategory) (hX : Simple X) (hY : Simple Y)
    (f : X ⟶ Y) (hf : f ≠ 0) : IsIso f := by
  let F := Legacy.evenToTotal (StatementLegacy.toLegacySupercategory C.toSupercategory)
  haveI : Simple Y := hY
  have htf : StatementLegacy.evenPoint f ≠ 0 := by
    exact fun h => hf ((Functor.map_eq_zero_iff F).mp h)
  haveI : @IsIso (Legacy.TotalCategory (StatementLegacy.toLegacySupercategory C.toSupercategory))
      _ X Y (F.map f) :=
    C.graded_schur X Y hX hY 0 (StatementLegacy.evenPoint f)
      (by
        rw [StatementLegacy.StatementBridge.grade_mem_iff]
        exact Legacy.evenPoint_mem_grade (StatementLegacy.toLegacySupercategory C.toSupercategory) f) htf
  haveI : Mono f := F.mono_of_mono_map inferInstance
  exact isIso_of_mono_of_nonzero hf

/-- Abelian structure recovered from the established finite semisimple models. -/
@[implicit_reducible] def statementAbelian (C : StatementLegacy.FusionPiSupercategory) :
    Abelian (StatementLegacy.Even C.toSupercategory) := by
  letI : HasFiniteBiproducts (StatementLegacy.Even C.toSupercategory) := C.biproducts
  exact EnrichedSupport.abelianOfSemisimple C.semisimple (statementEvenSchur C)

end RMod.EnrichedBridge
