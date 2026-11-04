import RMod.BrundanEllis.StackingProductFusion
import RMod.BrundanEllis.StackingCompletedPairing
import RMod.BrundanEllis.StackingHull
import RMod.BrundanEllis.StackingPairing

/-! The Deligne product is the intrinsic enriched idempotent completion
of the raw super tensor product. Separate additivity supplies all finite
sums, while the source parity object supplies parity shifts. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
open Stacking

def deligne (A B : WeaklyPointedFusionPiSuperCat) : WeaklyPointedFusionPiSuperCat :=
  { carrier := ProductCompletion A B }

def delignePairing (A B : WeaklyPointedFusionPiSuperCat) :
    SuperFunctor (SuperTensorProduct A B) (deligne A B) :=
  KaroubiSuper.embedding (SuperTensorProduct A B)

def deligneMonoidal (A B : WeaklyPointedFusionPiSuperCat) :
    (evenPair (delignePairing A B)).CoreMonoidal := completedPairMonoidal A B

/-- The intrinsic pairing has the fixed Koszul tensor, all-degree Hom
isomorphisms and precisely the required finite completion. -/
theorem deligne_data (A B : WeaklyPointedFusionPiSuperCat) :
    let D := deligne A B
    let F := delignePairing A B
    let M := deligneMonoidal A B
    (∀ X X' Y Y' : Even A × Even B,
      (F.map X X' ⊗ₘ F.map Y Y') ≫
        enrichedTensorMap (C := D) (MonoidalSuperCategory.tensor (C := D))
          MonoidalSuperCategory.tensor_objects _ _ _ _ ≫
        eHomWhiskerLeft SuperVec (C := Even D) _ (M.μIso X' Y').hom =
      tensorμ _ _ _ _ ≫
        (enrichedTensorMap (C := A) (MonoidalSuperCategory.tensor (C := A))
          MonoidalSuperCategory.tensor_objects X.1 X'.1 Y.1 Y'.1 ⊗ₘ
         enrichedTensorMap (C := B) (MonoidalSuperCategory.tensor (C := B))
          MonoidalSuperCategory.tensor_objects X.2 X'.2 Y.2 Y'.2) ≫
        F.map (X ⊗ Y : Even A × Even B) (X' ⊗ Y' : Even A × Even B) ≫
        eHomWhiskerRight SuperVec (C := Even D) (M.μIso X Y).hom _) ∧
    (∀ X Y a, Function.Bijective (F.map X Y a)) ∧
    (∀ X : Even D, AddPiHull D (fun Z => evenObj D (F.obj Z)) X)  := by
  refine ⟨completedPair_tensor_natural A B, KaroubiSuper.embedding_bijective _, ?_⟩
  intro X
  exact AddPiHull.of_retract (completedRetract X)
    (AddPiHull.generator (ForgetEnrichment.to SuperVec (ForgetEnrichment.to SuperVec X).X))

end RMod.BrundanEllis
