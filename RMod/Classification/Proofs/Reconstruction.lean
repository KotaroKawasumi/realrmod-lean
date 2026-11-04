import RMod.Classification.Instances.ReconstructionTwist
import RMod.Classification.Proofs.ReconstructionSuperequivalence
import RMod.Classification.Instances.TwistedPullback

/-!
# Exhaustiveness of the abstract pullback-and-twist construction

The intrinsic simple-orbit group and the extracted cochains form a lawful
twist. The specified superlinear equivalence, with its proved strong
monoidal structure, identifies the original category with that model.
The reference category remains an arbitrary category satisfying P.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem reconstruction (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (A : PiSuperfusion.{0, 0}) :
    ∃ t : Twist, Equivalent A (twistedPullback C hC t) := by
  let C₀ : PiSuperfusion := ⟨C, hC.toPiSuperfusionLaws⟩
  refine ⟨reconstructionTwist A C₀ hC, ⟨?_⟩⟩
  exact ⟨reconstructionSuperequivalenceData A C₀ hC,
    reconstructionSuperequivalenceLaws A C₀ hC⟩

end RMod.Classification
