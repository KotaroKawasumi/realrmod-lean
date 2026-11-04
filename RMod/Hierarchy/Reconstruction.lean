import RMod.Hierarchy.Constructions
import RMod.Hierarchy.Bridge.OldEquivalence
import RMod.Hierarchy.Bridge.RoundtripEquivalence
import RMod.Hierarchy.Instances.EquivalenceComposition
import RMod.Classification.Proofs.Reconstruction
import RMod.Classification.Proofs.SignReconstruction

/-!
# Reconstruction in the enriched hierarchy

The existing classification proof is applied to the verified old
presentation. Its equivalence is enriched and composed with the round-trip
comparison. No additional classification assumptions are introduced.
-/

noncomputable section
set_option autoImplicit false
namespace RMod.Legacy

theorem reconstruction (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSupercategory) :
    ∃ t : Twist, MonoidallySuperequivalent A (twistedPullback C hC t) := by
  obtain ⟨t, ⟨E⟩⟩ := Classification.reconstruction
    (Hierarchy.toOldPiSuperfusion C).data (Hierarchy.toOldReference C hC)
    (Hierarchy.toOldPiSuperfusion A)
  exact ⟨Twist.ofOld t, ⟨(Hierarchy.roundtripEquivalence A).comp
    (Hierarchy.ofOldMonoidalSuperequivalence E)⟩⟩

theorem sign_reconstruction (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSupercategory) :
    ∃ t : Twist, (∀ g h k, t.data.omega g h k = 1 ∨ t.data.omega g h k = -1) ∧
      MonoidallySuperequivalent A (twistedPullback C hC t) := by
  obtain ⟨t, ht, ⟨E⟩⟩ := Classification.sign_reconstruction
    (Hierarchy.toOldPiSuperfusion C).data (Hierarchy.toOldReference C hC)
    (Hierarchy.toOldPiSuperfusion A)
  exact ⟨Twist.ofOld t, ht, ⟨(Hierarchy.roundtripEquivalence A).comp
    (Hierarchy.ofOldMonoidalSuperequivalence E)⟩⟩

end RMod.Legacy
