import RMod.BrundanEllis.StackingExternalReversedFaithful
import RMod.BrundanEllis.StackingExternalGeneration
import RMod.BrundanEllis.StackingExternalCompletion

/-! Reversing the tensor order preserves generation of the external model.
This supplies the underlying completed equivalence with the order required
by the specified nu formula, without assuming a monoidal comparison. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.Limits
namespace RMod.BrundanEllis.Stacking

/-- Every target object is in the additive parity hull of reversed exterior images. -/
theorem reversedExteriorPairing_generates (s t : Twist) (W : Even (exteriorModel s t)) :
    AddPiHull (exteriorModel s t)
      (fun Z => evenObj (exteriorModel s t) ((reversedExteriorPairing s t).obj Z)) W := by
  have hgen : ∀ Z : SuperTensorProduct (pullback t) (pullback s),
      AddPiHull (exteriorModel s t)
        (fun U => evenObj (exteriorModel s t) ((reversedExteriorPairing s t).obj U))
        ((reverseExterior s t).forget.obj (evenObj (exteriorModel t s) ((exteriorPairing t s).obj Z))) := by
    intro Z
    exact AddPiHull.generator (Z.2, Z.1)
  have h := AddPiHull.map_super (reverseExterior s t) hgen
    (exteriorPairing_generates t s (evenObj (exteriorModel t s) (reverseExteriorObject t s W)))
  change AddPiHull (exteriorModel s t)
    (fun Z => evenObj (exteriorModel s t) ((reversedExteriorPairing s t).obj Z))
    (evenObj (exteriorModel s t) (reverseExteriorObject s t (reverseExteriorObject t s W))) at h
  rw [reverseExteriorObject_twice] at h
  exact h

/-- The reversed pairing realizes the ordinary even idempotent completion. -/
def reversedExteriorCompletionEquivalence (s t : Twist) :
    Even (PullbackProductCompletion s t) ≌ Even (exteriorModel s t) :=
  KaroubiSuper.realization (reversedExteriorPairing s t) (reversedExteriorPairing_bijective s t)
    (fun W => by
      obtain ⟨X, Y, h⟩ := pairHull_retract (reversedExteriorPairing s t)
        (reversedExteriorPairing_generates s t W)
      exact ⟨evenObj _ (X, Y), h⟩)

end RMod.BrundanEllis.Stacking
