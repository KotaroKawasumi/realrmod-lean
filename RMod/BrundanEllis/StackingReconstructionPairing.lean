import RMod.BrundanEllis.StackingPullbackProductCategory
import RMod.BrundanEllis.StackingEquivalenceFaithful
import RMod.BrundanEllis.StackingTensorFaithful

/-! Reconstruction is used only to establish finiteness and semisimplicity
of the intrinsic completed product. Tensor, parity and duality on that
product remain the explicit componentwise Karoubi constructions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking

/-- A chosen reconstructed presentation, without modifying the source category. -/
def reconstructedTwist (A : WeaklyPointedFusionPiSuperCat) : Twist :=
  (reconstruction realRMod real_isBrauerWallReference A).choose

def reconstructedEquivalence (A : WeaklyPointedFusionPiSuperCat) :
    MonoidalSuperequivalence A (pullback (reconstructedTwist A)) :=
  (reconstruction realRMod real_isBrauerWallReference A).choose_spec.some

abbrev ProductCompletion (A B : WeaklyPointedFusionPiSuperCat) :=
  Karoubi (Even (SuperTensorProduct A B))

def reconstructedProduct (A B : WeaklyPointedFusionPiSuperCat) : WeaklyPointedFusionPiSuperCat :=
  pullbackProductCategory (reconstructedTwist A) (reconstructedTwist B)

def reconstructedPairing (A B : WeaklyPointedFusionPiSuperCat) :
    SuperFunctor (SuperTensorProduct A B) (reconstructedProduct A B) :=
  (RMod.tensorEnrichedFunctors SuperVec (reconstructedEquivalence A).forward
    (reconstructedEquivalence B).forward).comp SuperVec
      (KaroubiSuper.embedding (SuperTensorProduct (pullback (reconstructedTwist A))
        (pullback (reconstructedTwist B))))

theorem reconstructedPairing_bijective (A B : WeaklyPointedFusionPiSuperCat)
    (X Y : SuperTensorProduct A B) (a : ZMod 2) :
    Function.Bijective ((reconstructedPairing A B).map X Y a) :=
by
  unfold reconstructedPairing
  apply comp_functors_bijective
  · exact tensor_functors_bijective (reconstructedEquivalence A).forward
      (reconstructedEquivalence B).forward (equivalence_bijective (reconstructedEquivalence A))
      (equivalence_bijective (reconstructedEquivalence B))
  · exact KaroubiSuper.embedding_bijective _

/-- Every target corner retracts to an image pair, using the two counit isomorphisms. -/
theorem reconstructedPairing_dense (A B : WeaklyPointedFusionPiSuperCat)
    (W : Even (reconstructedProduct A B)) :
    ∃ X : Even (SuperTensorProduct A B),
      Nonempty (Retract W ((reconstructedPairing A B).forget.obj X)) := by
  let E := reconstructedEquivalence A
  let H := reconstructedEquivalence B
  let Y := (ForgetEnrichment.to SuperVec W).X
  let S := E.backward.forget.obj (evenObj _ (ForgetEnrichment.to SuperVec Y).1)
  let T := H.backward.forget.obj (evenObj _ (ForgetEnrichment.to SuperVec Y).2)
  let J := KaroubiSuper.embedding (SuperTensorProduct (pullback (reconstructedTwist A))
    (pullback (reconstructedTwist B)))
  let e := (evenPairFunctor J).mapIso
    (CategoryTheory.Iso.prod (E.counit.app (evenObj _ (ForgetEnrichment.to SuperVec Y).1))
      (H.counit.app (evenObj _ (ForgetEnrichment.to SuperVec Y).2)))
  exact ⟨evenObj _ (S, T), ⟨(completedRetract W).trans (Retract.ofIso e.symm)⟩⟩

/-- The auxiliary comparison identifies the tensor units by the given reconstruction data. -/
def reconstructedPairingUnitIso (A B : WeaklyPointedFusionPiSuperCat) :
    (reconstructedPairing A B).forget.obj (𝟙_ (Even (SuperTensorProduct A B))) ≅
      𝟙_ (Even (reconstructedProduct A B)) :=
  (evenPairFunctor (KaroubiSuper.embedding
    (SuperTensorProduct (pullback (reconstructedTwist A)) (pullback (reconstructedTwist B))))).mapIso
    (CategoryTheory.Iso.prod (reconstructedEquivalence A).monoidal.εIso.symm
      (reconstructedEquivalence B).monoidal.εIso.symm)

end RMod.BrundanEllis.Stacking
