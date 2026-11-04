import RMod.BrundanEllis.StackingAmbientTensorWhisker

/-! Compose full enriched tensor naturality when the second comparison need not be invertible everywhere. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalSuperCategory C]
variable {D E : Type} [SuperCategory D] [SuperCategory E]
  [MonoidalCategory (Even D)] [MonoidalCategory (Even E)]
  [MonoidalSuperCategory D] [MonoidalSuperCategory E]
  (F : SuperFunctor C D) (G : SuperFunctor D E)
  (M : F.forget.CoreMonoidal)
  (ν : ∀ X Y : Even D, G.forget.obj X ⊗ G.forget.obj Y ⟶ G.forget.obj (X ⊗ Y))

/-- All-degree tensor naturality is preserved by composition. -/
theorem composite_relative_tensor_natural
    (hM : ∀ X X' Y Y' : Even C,
      (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
      KaroubiSuper.ambientTensor X X' Y Y' ≫
        F.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')))
    (hN : ∀ X X' Y Y' : Even D,
      (G.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        G.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        KaroubiSuper.ambientTensor (G.forget.obj X) (G.forget.obj X') (G.forget.obj Y) (G.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (G.forget.obj X ⊗ G.forget.obj Y) (ν X' Y') =
      KaroubiSuper.ambientTensor X X' Y Y' ≫
        G.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (ν X Y) (G.forget.obj (X' ⊗ Y')))
    (X X' Y Y' : Even C) :
    let H := F.comp SuperVec G
    (H.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      H.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (H.forget.obj X) (H.forget.obj X') (H.forget.obj Y) (H.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (H.forget.obj X ⊗ H.forget.obj Y)
        (ν (F.forget.obj X') (F.forget.obj Y') ≫ G.forget.map (M.μIso X' Y').hom) =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      H.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec (ν (F.forget.obj X) (F.forget.obj Y) ≫ G.forget.map (M.μIso X Y).hom)
        (H.forget.obj (X' ⊗ Y')) := by
  dsimp only
  dsimp only [EnrichedFunctor.comp]
  rw [eHomWhiskerLeft_comp]
  simp only [assoc]
  rw [← tensorHom_comp_tensorHom_assoc]
  erw [reassoc_of% (hN (F.forget.obj X) (F.forget.obj X')
    (F.forget.obj Y) (F.forget.obj Y'))]
  erw [← eHom_whisker_exchange]
  rw [superFunctor_post_assoc]
  erw [reassoc_of% (hM X X' Y Y')]
  rw [← superFunctor_pre_assoc]
  simp only [assoc, eHomWhiskerRight_comp]
  rfl

end RMod.BrundanEllis.Stacking
