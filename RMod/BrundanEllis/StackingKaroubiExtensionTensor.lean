import RMod.BrundanEllis.StackingKaroubiExtensionMonoidal
import RMod.BrundanEllis.StackingKaroubiEmbeddingTensor
import RMod.BrundanEllis.StackingKaroubiFunctorTensor

/-! Splitting idempotents and extending a functor preserve tensor naturality
on every homogeneous degree. The ordinary coherence is the existing one. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [MonoidalSuperCategory C] [MonoidalSuperCategory D]
  [IsIdempotentComplete (Even D)]

/-- Splitting an even idempotent retains tensor naturality on the entire
Hom object, including odd arrows. -/
theorem retraction_tensor_natural (X X' Y Y' : Even (Karoubi (Even D))) :
    ((retraction D).map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      (retraction D).map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      ambientTensor ((retraction D).forget.obj X) ((retraction D).forget.obj X')
        ((retraction D).forget.obj Y) ((retraction D).forget.obj Y') ≫
      eHomWhiskerLeft SuperVec ((retraction D).forget.obj X ⊗ (retraction D).forget.obj Y)
        ((retractionMonoidal (D := D)).μIso X' Y').hom =
    completedTensorMap X X' Y Y' ≫
      (retraction D).map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec ((retractionMonoidal (D := D)).μIso X Y).hom
        ((retraction D).forget.obj (X' ⊗ Y')) := by
  exact enrichedInverse_tensor_natural (embedding D) (embedding_bijective D)
    (retractObject D) (retractComparison D) (embeddingMonoidal D)
    (fun A A' B B' => embedding_tensor_natural A A' B B') X X' Y Y'

/-- The actual enriched extension to idempotent completion is monoidal in
all degrees whenever the original functor is. -/
theorem extension_tensor_natural (F : SuperFunctor C D) (M : F.forget.CoreMonoidal)
    (h : ∀ X X' Y Y' : Even C,
      (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
      ambientTensor X X' Y Y' ≫ F.map (ForgetEnrichment.to SuperVec (X ⊗ Y))
        (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')))
    (X X' Y Y' : Even (Karoubi (Even C))) :
    ((extension F).map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      (extension F).map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      ambientTensor ((extension F).forget.obj X) ((extension F).forget.obj X')
        ((extension F).forget.obj Y) ((extension F).forget.obj Y') ≫
      eHomWhiskerLeft SuperVec ((extension F).forget.obj X ⊗ (extension F).forget.obj Y)
        ((extensionMonoidal F M).μIso X' Y').hom =
    completedTensorMap X X' Y Y' ≫
      (extension F).map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec ((extensionMonoidal F M).μIso X Y).hom
        ((extension F).forget.obj (X' ⊗ Y')) := by
  exact composite_tensor_natural (functor F) (retraction D)
    (functorMonoidal F M) (retractionMonoidal (D := D))
    (fun A A' B B' => functor_tensor_natural F M h A A' B B')
    (fun A A' B B' => retraction_tensor_natural A A' B B') X X' Y Y'

end RMod.BrundanEllis.Stacking.KaroubiSuper
