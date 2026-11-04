import RMod.Hierarchy.Reconstruction
import RMod.Hierarchy.Bridge.ReflectEquivalence
import RMod.Classification.Proofs.GaugeCriterion

/-!
# The gauge classification in the enriched hierarchy

Necessity reflects a supplied enriched equivalence to the old presentation.
Sufficiency enriches the old equivalence constructed from gauge data.
-/

noncomputable section
set_option autoImplicit false
namespace RMod.Legacy

theorem equivalence_iff_gauge (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (s t : Twist) :
    MonoidallySuperequivalent (twistedPullback C hC s) (twistedPullback C hC t) ↔
      GaugeEquivalent s.data t.data := by
  rw [gaugeEquivalent_iff_old]
  constructor
  · rintro ⟨E⟩
    exact (Classification.equivalence_iff_gauge (Hierarchy.toOldPiSuperfusion C).data
      (Hierarchy.toOldReference C hC) s.toOld t.toOld).mp ⟨Hierarchy.reflectEquivalence E⟩
  · intro h
    obtain ⟨E⟩ := (Classification.equivalence_iff_gauge (Hierarchy.toOldPiSuperfusion C).data
      (Hierarchy.toOldReference C hC) s.toOld t.toOld).mpr h
    exact ⟨Hierarchy.ofOldMonoidalSuperequivalence E⟩

end RMod.Legacy
