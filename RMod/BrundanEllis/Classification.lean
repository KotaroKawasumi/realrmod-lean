import RMod.BrundanEllis.FusionBridge
import RMod.BrundanEllis.Gauge

/-! The Brundan--Ellis declaration surface receives the four existing
classification theorems through proved parity and monoidal conversions.
The completed models retain their original computational constructions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace RMod.BrundanEllis
open Bridge

/-- Construct the real model, including its fusion, split-unit, and weak-pointedness proofs. -/
def realRMod : WeaklyPointedFusionPiSuperCat := fromStage RMod.realRMod

/-- Construct the completed model assigned to a reference category and a twist. -/
def twistedPullback (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (t : Twist) : WeaklyPointedFusionPiSuperCat :=
  fromStage (RMod.twistedPullback (toStage C) (toReference C hC) (toTwist t))

/-- The constructed real model is a Brauer-Wall reference category. -/
theorem real_isBrauerWallReference : IsBrauerWallReference realRMod :=
  fromReference RMod.realRMod RMod.real_isBrauerWallReference

/-- Every weakly pointed category is monoidally superequivalent to a twisted pullback. -/
theorem reconstruction (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSuperCat) :
    ∃ t : Twist, MonoidallySuperequivalent A (twistedPullback C hC t) := by
  obtain ⟨t, e⟩ := RMod.reconstruction (toStage C) (toReference C hC) (toStage A)
  exact ⟨fromTwist t, fromStageEquivalence _ _ e⟩

/-- Two constructed models are monoidally superequivalent exactly when their twists are gauge equivalent. -/
theorem equivalence_iff_gauge (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (s t : Twist) :
    MonoidallySuperequivalent (twistedPullback C hC s) (twistedPullback C hC t) ↔
      GaugeEquivalent s t := by
  rw [gauge_iff]
  rw [← RMod.equivalence_iff_gauge (toStage C) (toReference C hC) (toTwist s) (toTwist t)]
  exact ⟨toStageEquivalence (twistedPullback C hC s) (twistedPullback C hC t),
    fromStageEquivalence (twistedPullback C hC s) (twistedPullback C hC t)⟩

/-- Reconstruction can be achieved with every associator scalar equal to a real sign. -/
theorem sign_reconstruction (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSuperCat) :
    ∃ t : Twist, (∀ g h k, t.omega g h k = 1 ∨ t.omega g h k = -1) ∧
      MonoidallySuperequivalent A (twistedPullback C hC t) := by
  obtain ⟨t, ht, e⟩ := RMod.sign_reconstruction (toStage C) (toReference C hC) (toStage A)
  exact ⟨fromTwist t, ht, fromStageEquivalence _ _ e⟩

end RMod.BrundanEllis
