import RMod.BrundanEllis.StackingKaroubiRealization
import RMod.BrundanEllis.StackingExternalFaithful
import RMod.BrundanEllis.StackingExternalGeneration
import RMod.BrundanEllis.StackingPairRetracts
import RMod.BrundanEllis.StackingSemisimpleTransfer

/-! The specified exterior model realizes the ordinary even category of the
completed super tensor product of two pullbacks. This supplies abelianity
and finite semisimple decompositions independently of the monoidal comparison. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking

abbrev PullbackProductCompletion (s t : Twist) := Karoubi (Even (SuperTensorProduct (pullback s) (pullback t)))

/-- The all-degree faithful pairing and proved generation give an ordinary equivalence. -/
def exteriorCompletionEquivalence (s t : Twist) :
    Even (PullbackProductCompletion s t) ≌ Even (exteriorModel s t) :=
  KaroubiSuper.realization (exteriorPairing s t) (exteriorPairing_bijective s t)
    (fun W => by
      obtain ⟨X, Y, h⟩ := pairHull_retract (exteriorPairing s t) (exteriorPairing_generates s t W)
      exact ⟨evenObj _ (X, Y), h⟩)

instance pullbackProductAbelian (s t : Twist) : Abelian (Even (PullbackProductCompletion s t)) := by
  let F := (exteriorCompletionEquivalence s t).functor
  letI : HasFiniteProducts (Even (PullbackProductCompletion s t)) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence F⟩
  exact abelianOfEquivalence F

theorem pullbackProductSemisimple (s t : Twist) (X : Even (PullbackProductCompletion s t)) :
    ∃ (n : ℕ) (S : Fin n → Even (PullbackProductCompletion s t)),
      (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S) :=
  semisimple_of_equivalence (exteriorCompletionEquivalence s t)
    (FusionPiSuperCategory.semisimple (C := exteriorModel s t)) X

end RMod.BrundanEllis.Stacking
