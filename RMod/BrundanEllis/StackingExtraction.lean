import RMod.BrundanEllis.StackingStack
import RMod.BrundanEllis.StackingIntrinsicOrbits

/-! Extract the actual reconstruction cochains from the completed diagonal.
The group is its intrinsic simple-parity-orbit group. Identifying that group
with the input labels and computing a closed formula are separate obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking

/-- Reuse the concrete component comparisons and associator routes of reconstruction. -/
def extractedOldTwist (A : WeaklyPointedFusionPiSuperCat) : RMod.Classification.Twist :=
  RMod.Classification.reconstructionTwist (intrinsicOld A) reference referenceProperty

/-- Only the interface changes: all four fields of the reconstructed data are retained. -/
def extractedTwist (A : WeaklyPointedFusionPiSuperCat) : Twist :=
  Bridge.fromTwist (RMod.EnrichedBridge.fromTwist
    (RMod.StatementLegacy.Twist.ofOld (extractedOldTwist A)))

/-- This specifies the actual cochains rather than choosing an unspecified existential witness. -/
theorem extractedTwist_data (A : WeaklyPointedFusionPiSuperCat) :
    (extractedTwist A).toTwistData =
      ⟨intrinsicOrbitGroup A, RMod.Classification.intrinsicRho (intrinsicOld A),
        RMod.Classification.reconstructionNu (intrinsicOld A) reference referenceProperty,
        RMod.Classification.reconstructionOmega (intrinsicOld A) reference referenceProperty⟩ := rfl

private theorem extracted_legacy (A : WeaklyPointedFusionPiSuperCat) :
    RMod.Legacy.MonoidallySuperequivalent (intrinsicLegacy A)
      (RMod.Legacy.twistedPullback legacyReference legacyReferenceProperty
        (RMod.Legacy.Twist.ofOld (extractedOldTwist A))) := by
  let E : RMod.Classification.MonoidalSuperequivalence (intrinsicOld A).toWeaklyPointedSuperfusion
      (RMod.Classification.twistedPullback reference.data referenceProperty (extractedOldTwist A)).toWeaklyPointedSuperfusion :=
    ⟨RMod.Classification.reconstructionSuperequivalenceData (intrinsicOld A) reference referenceProperty,
      RMod.Classification.reconstructionSuperequivalenceLaws (intrinsicOld A) reference referenceProperty⟩
  exact ⟨(RMod.Legacy.Hierarchy.roundtripEquivalence (intrinsicLegacy A)).comp
    (RMod.Legacy.Hierarchy.ofOldMonoidalSuperequivalence E)⟩

private theorem extracted_statement (A : WeaklyPointedFusionPiSuperCat) :
    RMod.StatementLegacy.MonoidallySuperequivalent
      (RMod.EnrichedBridge.toWeak (Bridge.toStage A))
      (RMod.StatementLegacy.twistedPullback
        (RMod.EnrichedBridge.toWeak (Bridge.toStage realRMod))
        (RMod.EnrichedBridge.toReference _ (Bridge.toReference realRMod real_isBrauerWallReference))
        (RMod.StatementLegacy.Twist.ofOld (extractedOldTwist A))) := by
  obtain ⟨E⟩ := extracted_legacy A
  refine ⟨RMod.StatementLegacy.StatementBridge.fromEquivalence ?_⟩
  have hround (C : RMod.Legacy.WeaklyPointedFusionPiSupercategory) :
      RMod.StatementLegacy.StatementBridge.toMonoidal
          (RMod.StatementLegacy.StatementBridge.fromWeak C).toMonoidalPiSupercategory.monoidal =
        C.toMonoidalPiSupercategory.monoidal :=
    congrArg (fun D => D.toMonoidalPiSupercategory.monoidal)
      (RMod.StatementLegacy.StatementBridge.toWeak_fromWeak C)
  simp only [RMod.StatementLegacy.twistedPullback, hround,
    RMod.StatementLegacy.Twist.toOld_ofOld]
  with_unfolding_all exact E

/-- The supplied completed category is equivalent to the pullback of these exact cochains. -/
theorem extractedTwist_pullback (A : WeaklyPointedFusionPiSuperCat) :
    MonoidallySuperequivalent A (pullback (extractedTwist A)) := by
  obtain ⟨E⟩ := extracted_statement A
  apply Bridge.fromStageEquivalence
  exact ⟨RMod.EnrichedBridge.fromEquivalence _ _ E⟩

/-- The geometric output twist, before identifying its intrinsic group with the input group. -/
def stackExtractedTwist (s t : Twist) (h : s.group = t.group) : Twist :=
  extractedTwist (stack s t h)

theorem stackExtractedTwist_data (s t : Twist) (h : s.group = t.group) :
    (stackExtractedTwist s t h).toTwistData =
      ⟨intrinsicOrbitGroup (stack s t h),
        RMod.Classification.intrinsicRho (intrinsicOld (stack s t h)),
        RMod.Classification.reconstructionNu (intrinsicOld (stack s t h)) reference referenceProperty,
        RMod.Classification.reconstructionOmega (intrinsicOld (stack s t h)) reference referenceProperty⟩ := rfl

/-- Existence with a specified witness; this does not yet identify it with `twistMul`. -/
theorem stack_extracted_pullback (s t : Twist) (h : s.group = t.group) :
    MonoidallySuperequivalent (stack s t h) (pullback (stackExtractedTwist s t h)) :=
  extractedTwist_pullback (stack s t h)

end RMod.BrundanEllis.Stacking
