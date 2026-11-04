import RMod.BrundanEllis.StackingReconstructionPairing

/-! The intrinsic completed product of arbitrary weakly pointed categories
is finite semisimple. An auxiliary reconstructed comparison establishes
these properties and the split unit, without defining or replacing the
intrinsic tensor by transport from that comparison. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

def reconstructedCompletedFunctor (A B : WeaklyPointedFusionPiSuperCat) :
    SuperFunctor (ProductCompletion A B) (reconstructedProduct A B) :=
  KaroubiSuper.extension (reconstructedPairing A B)

theorem reconstructedCompleted_bijective (A B : WeaklyPointedFusionPiSuperCat)
    (X Y : ProductCompletion A B) (a : ZMod 2) :
    Function.Bijective ((reconstructedCompletedFunctor A B).map X Y a) := by
  unfold reconstructedCompletedFunctor
  apply KaroubiSuper.extension_bijective
  exact reconstructedPairing_bijective A B

def reconstructedCompletedEquivalence (A B : WeaklyPointedFusionPiSuperCat) :
    Even (ProductCompletion A B) ≌ Even (reconstructedProduct A B) :=
  KaroubiSuper.extensionEquivalence (reconstructedPairing A B)
    (reconstructedPairing_bijective A B) (reconstructedPairing_dense A B)

instance reconstructedCompleted_isEquivalence (A B : WeaklyPointedFusionPiSuperCat) :
    (reconstructedCompletedFunctor A B).forget.IsEquivalence :=
  (reconstructedCompletedEquivalence A B).isEquivalence_functor

instance productAbelian (A B : WeaklyPointedFusionPiSuperCat) :
    Abelian (Even (ProductCompletion A B)) := by
  let F := (reconstructedCompletedEquivalence A B).functor
  letI : HasFiniteProducts (Even (ProductCompletion A B)) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence F⟩
  exact abelianOfEquivalence F

theorem productSemisimple (A B : WeaklyPointedFusionPiSuperCat) (X : Even (ProductCompletion A B)) :
    ∃ (n : ℕ) (S : Fin n → Even (ProductCompletion A B)),
      (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S) :=
  semisimple_of_equivalence (reconstructedCompletedEquivalence A B)
    (FusionPiSuperCategory.semisimple (C := reconstructedProduct A B)) X

theorem productFiniteOrbits (A B : WeaklyPointedFusionPiSuperCat) :
    ∃ (n : ℕ) (S : Fin n → Even (ProductCompletion A B)),
      (∀ i, Simple (S i)) ∧ ∀ X : Even (ProductCompletion A B), Simple X →
        ∃ i, SameParityOrbit (ProductCompletion A B) X (S i) :=
  finite_orbits_of_equivalence (reconstructedCompletedFunctor A B)
    (reconstructedCompleted_bijective A B)
    (FusionPiSuperCategory.finite_simples (C := reconstructedProduct A B))

def reconstructedCompletedUnitIso (A B : WeaklyPointedFusionPiSuperCat) :
    (reconstructedCompletedFunctor A B).forget.obj (𝟙_ (Even (ProductCompletion A B))) ≅
      𝟙_ (Even (reconstructedProduct A B)) :=
  KaroubiSuper.extensionEmbeddingIso (reconstructedPairing A B)
    (𝟙_ (Even (SuperTensorProduct A B))) ≪≫ reconstructedPairingUnitIso A B

theorem productSimpleUnit (A B : WeaklyPointedFusionPiSuperCat) :
    Simple (𝟙_ (Even (ProductCompletion A B))) := by
  letI := FusionPiSuperCategory.simple_unit (C := reconstructedProduct A B)
  letI : Simple ((reconstructedCompletedEquivalence A B).functor.obj
      (𝟙_ (Even (ProductCompletion A B)))) := Simple.of_iso (reconstructedCompletedUnitIso A B)
  exact simple_reflects_equivalence (reconstructedCompletedEquivalence A B) _

theorem productSplitUnit (A B : WeaklyPointedFusionPiSuperCat) :
    IsSplitUnit (ProductCompletion A B) := by
  obtain ⟨e⟩ := WeaklyPointedFusionPiSuperCategory.splitUnit (C := reconstructedProduct A B)
  exact ⟨(endEquivalenceOfIso (reconstructedCompletedFunctor A B)
    (reconstructedCompleted_bijective A B) _ _ (reconstructedCompletedUnitIso A B)).trans e⟩

instance productFusion (A B : WeaklyPointedFusionPiSuperCat) :
    FusionPiSuperCategory (ProductCompletion A B) where
  hom_finite := completed_product_hom_finite A B
  semisimple := productSemisimple A B
  finite_simples := productFiniteOrbits A B
  simple_unit := productSimpleUnit A B

instance productWeaklyPointed (A B : WeaklyPointedFusionPiSuperCat) :
    WeaklyPointedFusionPiSuperCategory (ProductCompletion A B) where
  splitUnit := productSplitUnit A B
  weaklyPointed := completed_weaklyPointed A B

end RMod.BrundanEllis.Stacking
