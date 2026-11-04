import RMod.BrundanEllis.StackingAmbientTensorWhisker

/-! Compose ordinary monoidal structures and prove full enriched tensor naturality of the composite. -/
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
  (M : F.forget.CoreMonoidal) (N : G.forget.CoreMonoidal)

/-- Compose ordinary monoidal coherence along the canonical forgetful comparison. -/
def compositeCoreMonoidal : (F.comp SuperVec G).forget.CoreMonoidal := by
  letI := M.toMonoidal
  letI := N.toMonoidal
  letI := Functor.Monoidal.transport (EnrichedFunctor.forgetComp F G).symm
  exact Functor.CoreMonoidal.ofLaxMonoidal _

/-- The composite tensorator is the usual two-step comparison. -/
theorem compositeCoreMonoidal_tensor (X Y : Even C) :
    ((compositeCoreMonoidal F G M N).μIso X Y).hom =
      (N.μIso (F.forget.obj X) (F.forget.obj Y)).hom ≫ G.forget.map (M.μIso X Y).hom := by
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫
    ((N.μIso (F.forget.obj X) (F.forget.obj Y)).hom ≫ G.forget.map (M.μIso X Y).hom) ≫ 𝟙 _ = _
  simp only [id_tensorHom_id, Category.id_comp, Category.comp_id]

/-- All-degree tensor naturality is preserved by composition. -/
theorem composite_tensor_natural
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
        eHomWhiskerLeft SuperVec (G.forget.obj X ⊗ G.forget.obj Y) (N.μIso X' Y').hom =
      KaroubiSuper.ambientTensor X X' Y Y' ≫
        G.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (N.μIso X Y).hom (G.forget.obj (X' ⊗ Y')))
    (X X' Y Y' : Even C) :
    let H := F.comp SuperVec G
    (H.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      H.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (H.forget.obj X) (H.forget.obj X') (H.forget.obj Y) (H.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (H.forget.obj X ⊗ H.forget.obj Y)
        ((compositeCoreMonoidal F G M N).μIso X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      H.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec ((compositeCoreMonoidal F G M N).μIso X Y).hom
        (H.forget.obj (X' ⊗ Y')) := by
  dsimp only
  rw [compositeCoreMonoidal_tensor, compositeCoreMonoidal_tensor]
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
