import RMod.BrundanEllis.StackingExtraction
import RMod.BrundanEllis.StackingOperations
import RMod.Hierarchy.Instances.EquivalenceComposition

/-! The final categorical step is only composition. The remaining input
is an actual gauge identification of the extracted cochains with the
specified product; this lemma does not assume that identification silently. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace RMod.BrundanEllis.Stacking

/-- Compose public monoidal superequivalences through the established bridge. -/
theorem monoidallySuperequivalent_trans {A B C : WeaklyPointedFusionPiSuperCat}
    (hAB : MonoidallySuperequivalent A B) (hBC : MonoidallySuperequivalent B C) :
    MonoidallySuperequivalent A C := by
  obtain ⟨E⟩ := hAB
  obtain ⟨F⟩ := hBC
  exact ⟨Bridge.fromStatementEquivalence A C
    (RMod.StatementLegacy.StatementBridge.fromEquivalence
      ((RMod.StatementLegacy.StatementBridge.toEquivalence
        (Bridge.toStatementEquivalence A B E)).comp
        (RMod.StatementLegacy.StatementBridge.toEquivalence
          (Bridge.toStatementEquivalence B C F))))⟩

/-- Once the extracted twist is identified, stack_pullback is immediate. -/
theorem stack_pullback_of_extracted_gauge {G : FiniteGrp.{0}} (s t : TwistOn G)
    (h : GaugeEquivalent
      (stackExtractedTwist s.val t.val (s.property.trans t.property.symm))
      (twistMul s t).val) :
    MonoidallySuperequivalent (stack s.val t.val (s.property.trans t.property.symm))
      (pullback (twistMul s t).val) :=
  monoidallySuperequivalent_trans
    (stack_extracted_pullback s.val t.val (s.property.trans t.property.symm))
    ((equivalence_iff_gauge realRMod real_isBrauerWallReference _ _).mpr h)

end RMod.BrundanEllis.Stacking
