import RMod.Statement.ReferenceBridge
import RMod.Statement.EquivalenceBridge
import RMod.Statement.Gauge
import RMod.Hierarchy.Classification

/-!
# Classification in the Mathlib-based completed hierarchy

The existing construction and classification proofs are reused through the
previous enriched hierarchy. The same construction is used in reconstruction,
the gauge criterion, and normalization to real signs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.StatementLegacy
open StatementBridge

/-- Construct the real model together with its fusion and weak-pointedness proofs. -/
def realRMod : WeaklyPointedFusionPiSupercategory :=
  fromWeak Legacy.realFusionPiSupercategory

theorem real_isBrauerWallReference : IsBrauerWallReference realRMod :=
  fromReference Legacy.realFusionPiSupercategory Legacy.real_isBrauerWallReference

/-- Reuse the established pullback and twist of the supplied reference category. -/
def twistedPullback (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (t : Twist) : WeaklyPointedFusionPiSupercategory :=
  fromWeak (Legacy.twistedPullback (toWeak C) (toReference C hC) (Legacy.Twist.ofOld t.toOld))

private theorem toMonoidal_fromWeak (C : Legacy.WeaklyPointedFusionPiSupercategory) :
    toMonoidal (fromWeak C).toMonoidalPiSupercategory.monoidal =
      C.toMonoidalPiSupercategory.monoidal :=
  congrArg (fun D => D.toMonoidalPiSupercategory.monoidal) (toWeak_fromWeak C)

/-- Every weakly pointed category is realized by the same constructed family. -/
theorem reconstruction (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSupercategory) :
    ∃ t : Twist, MonoidallySuperequivalent A (twistedPullback C hC t) := by
  obtain ⟨t, ⟨E⟩⟩ := Legacy.reconstruction (toWeak C) (toReference C hC) (toWeak A)
  refine ⟨Twist.ofOld t.toOld, ⟨fromEquivalence ?_⟩⟩
  simp only [twistedPullback, toMonoidal_fromWeak, Twist.toOld_ofOld,
    Legacy.Twist.ofOld_toOld]
  exact E

/-- The constructed family identifies precisely the fixed gauge classes. -/
theorem equivalence_iff_gauge (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (s t : Twist) :
    MonoidallySuperequivalent (twistedPullback C hC s) (twistedPullback C hC t) ↔
      GaugeEquivalent s.data t.data := by
  rw [gaugeEquivalent_iff_old]
  have hg := (Legacy.equivalence_iff_gauge (toWeak C) (toReference C hC)
    (Legacy.Twist.ofOld s.toOld) (Legacy.Twist.ofOld t.toOld)).trans
      (Legacy.gaugeEquivalent_iff_old _ _)
  constructor
  · rintro ⟨E⟩
    apply hg.mp
    refine ⟨?_⟩
    simpa only [twistedPullback, toMonoidal_fromWeak] using toEquivalence E
  · intro h
    obtain ⟨E⟩ := hg.mpr h
    refine ⟨fromEquivalence ?_⟩
    simpa only [twistedPullback, toMonoidal_fromWeak] using E

/-- The existing sign-normalized reconstruction keeps the same model function. -/
theorem sign_reconstruction (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSupercategory) :
    ∃ t : Twist, (∀ g h k, t.data.omega g h k = 1 ∨ t.data.omega g h k = -1) ∧
      MonoidallySuperequivalent A (twistedPullback C hC t) := by
  obtain ⟨t, ht, ⟨E⟩⟩ := Legacy.sign_reconstruction (toWeak C) (toReference C hC) (toWeak A)
  refine ⟨Twist.ofOld t.toOld, ht, ⟨fromEquivalence ?_⟩⟩
  simp only [twistedPullback, toMonoidal_fromWeak, Twist.toOld_ofOld,
    Legacy.Twist.ofOld_toOld]
  exact E

end RMod.StatementLegacy
