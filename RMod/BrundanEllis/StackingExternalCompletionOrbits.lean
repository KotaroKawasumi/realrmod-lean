import RMod.BrundanEllis.StackingExternalCompletion
import RMod.BrundanEllis.StackingKaroubiExtension
import RMod.BrundanEllis.StackingFiniteOrbitTransfer

/-! The exterior model comparison is available on all homogeneous morphisms.
Its ordinary equivalence transports the finite simple parity-orbit list to
the same completed product on which tensor, duals and pi were constructed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.BrundanEllis.Stacking

/-- Extension of the concrete exterior pairing to all even corners. -/
def exteriorCompletedFunctor (s t : Twist) :
    SuperFunctor (PullbackProductCompletion s t) (exteriorModel s t) :=
  KaroubiSuper.extension (exteriorPairing s t)

theorem exteriorCompletedFunctor_bijective (s t : Twist)
    (P Q : PullbackProductCompletion s t) (a : ZMod 2) :
    Function.Bijective ((exteriorCompletedFunctor s t).map P Q a) :=
  KaroubiSuper.extension_bijective (exteriorPairing s t) (exteriorPairing_bijective s t) P Q a

/-- The ordinary equivalence with this specific enriched forward functor. -/
def exteriorCompletedEquivalence (s t : Twist) :
    Even (PullbackProductCompletion s t) ≌ Even (exteriorModel s t) :=
  KaroubiSuper.extensionEquivalence (exteriorPairing s t) (exteriorPairing_bijective s t)
    (fun W => by
      obtain ⟨X, Y, h⟩ := pairHull_retract (exteriorPairing s t) (exteriorPairing_generates s t W)
      exact ⟨evenObj _ (X, Y), h⟩)

instance exteriorCompletedFunctor_equivalence (s t : Twist) :
    (exteriorCompletedFunctor s t).forget.IsEquivalence :=
  (exteriorCompletedEquivalence s t).isEquivalence_functor

theorem pullbackProductFiniteOrbits (s t : Twist) :
    ∃ (n : ℕ) (S : Fin n → Even (PullbackProductCompletion s t)),
      (∀ i, Simple (S i)) ∧ ∀ X : Even (PullbackProductCompletion s t), Simple X →
        ∃ i, SameParityOrbit (PullbackProductCompletion s t) X (S i) :=
  finite_orbits_of_equivalence (exteriorCompletedFunctor s t)
    (exteriorCompletedFunctor_bijective s t)
    (FusionPiSuperCategory.finite_simples (C := exteriorModel s t))

end RMod.BrundanEllis.Stacking
