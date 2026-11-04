import RMod.Enriched.FromEquivalence
import RMod.Enriched.TwistBridge
import RMod.Statement.Classification

/-! The four classification theorems for the independent enriched statement
surface, obtained from the established classification by proved conversions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod
open EnrichedBridge

/-- The established real model, with its derived abelian even category. -/
def realRMod : WeaklyPointedFusionPiSuperCat := fromWeak StatementLegacy.realRMod

/-- The established completed pullback, transported to the enriched interface. -/
def twistedPullback (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (t : Twist) : WeaklyPointedFusionPiSuperCat :=
  fromWeak (StatementLegacy.twistedPullback (toWeak C) (toReference C hC) (toTwist t))

/-- The real model retains its classification of simple parity orbits. -/
theorem real_isBrauerWallReference : IsBrauerWallReference realRMod :=
  fromReference _ StatementLegacy.real_isBrauerWallReference

/-- Reconstruct arbitrary new inputs through the old classification and the full naturality bridge. -/
theorem reconstruction (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSuperCat) :
    ∃ t : Twist, MonoidallySuperequivalent A (twistedPullback C hC t) := by
  obtain ⟨t, ⟨e⟩⟩ := StatementLegacy.reconstruction (toWeak C) (toReference C hC) (toWeak A)
  refine ⟨fromTwist t, ⟨?_⟩⟩
  exact fromEquivalence _ _ e

/-- Gauge reachability agrees with monoidal superequivalence of the completed models. -/
theorem equivalence_iff_gauge (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (s t : Twist) :
    MonoidallySuperequivalent (twistedPullback C hC s) (twistedPullback C hC t) ↔
      GaugeEquivalent s t := by
  rw [gauge_iff]
  rw [← StatementLegacy.equivalence_iff_gauge (toWeak C) (toReference C hC) (toTwist s) (toTwist t)]
  constructor
  · rintro ⟨e⟩
    exact ⟨toEquivalence _ _ e⟩
  · rintro ⟨e⟩
    exact ⟨fromEquivalence _ _ e⟩

/-- The signed reconstruction theorem has exactly the same scalar normalization. -/
theorem sign_reconstruction (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSuperCat) :
    ∃ t : Twist, (∀ g h k, t.omega g h k = 1 ∨ t.omega g h k = -1) ∧
      MonoidallySuperequivalent A (twistedPullback C hC t) := by
  obtain ⟨t, ht, ⟨e⟩⟩ := StatementLegacy.sign_reconstruction (toWeak C) (toReference C hC) (toWeak A)
  exact ⟨fromTwist t, ht, ⟨fromEquivalence _ _ e⟩⟩

end RMod
