import RMod.BrundanEllis.StackingExternalCompletionOrbits
import RMod.BrundanEllis.StackingExternalUnit
import RMod.BrundanEllis.StackingEndTransport
import RMod.BrundanEllis.StackingHomFinite
import RMod.BrundanEllis.StackingPiStructures
import RMod.BrundanEllis.StackingProductRigid
import RMod.BrundanEllis.StackingKaroubiEvenRigid
import RMod.BrundanEllis.StackingKaroubiSuperMonoidal

/-! The completed product of two pullbacks has the fusion conditions and a
split real tensor unit. Tensor and duality come from the genuine enriched
Karoubi construction; the ordinary exterior model supplies semisimplicity
and finite simple parity orbits without an assumed monoidal comparison. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

def exteriorCompletedUnitIso (s t : Twist) :
    (exteriorCompletedFunctor s t).forget.obj (𝟙_ (Even (PullbackProductCompletion s t))) ≅
      𝟙_ (Even (exteriorModel s t)) :=
  KaroubiSuper.extensionEmbeddingIso (exteriorPairing s t)
    (𝟙_ (Even (SuperTensorProduct (pullback s) (pullback t)))) ≪≫ exteriorUnitIso s t

theorem pullbackProductSimpleUnit (s t : Twist) :
    Simple (𝟙_ (Even (PullbackProductCompletion s t))) := by
  letI := FusionPiSuperCategory.simple_unit (C := exteriorModel s t)
  letI : Simple ((exteriorCompletedEquivalence s t).functor.obj
      (𝟙_ (Even (PullbackProductCompletion s t)))) := Simple.of_iso (exteriorCompletedUnitIso s t)
  exact simple_reflects_equivalence (exteriorCompletedEquivalence s t) _

theorem pullbackProductSplitUnit (s t : Twist) : IsSplitUnit (PullbackProductCompletion s t) := by
  obtain ⟨e⟩ := WeaklyPointedFusionPiSuperCategory.splitUnit (C := exteriorModel s t)
  exact ⟨(endEquivalenceOfIso (exteriorCompletedFunctor s t)
    (exteriorCompletedFunctor_bijective s t) _ _ (exteriorCompletedUnitIso s t)).trans e⟩

instance pullbackProductFusion (s t : Twist) : FusionPiSuperCategory (PullbackProductCompletion s t) where
  hom_finite := completed_product_hom_finite (pullback s) (pullback t)
  semisimple := pullbackProductSemisimple s t
  finite_simples := pullbackProductFiniteOrbits s t
  simple_unit := pullbackProductSimpleUnit s t

end RMod.BrundanEllis.Stacking
