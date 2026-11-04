import RMod.BrundanEllis.StackingAmbientTensorWhisker
import RMod.BrundanEllis.StackingFaithfulForget

/-! Full enriched tensor naturality is reflected through a faithful forward functor using its compatible counit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalSuperCategory C]
variable {D : Type} [SuperCategory D] [MonoidalCategory (Even D)] [MonoidalSuperCategory D]
  (F : SuperFunctor C D) (G : SuperFunctor D C)
  (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
  (μF : ∀ X Y : Even C, F.forget.obj X ⊗ F.forget.obj Y ≅ F.forget.obj (X ⊗ Y))
  (μG : ∀ X Y : Even D, G.forget.obj X ⊗ G.forget.obj Y ≅ G.forget.obj (X ⊗ Y))
  (e : ∀ X : Even D, F.forget.obj (G.forget.obj X) ≅ X)
  (hM : ∀ X X' Y Y' : Even C,
    (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (μF X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫ F.map (ForgetEnrichment.to SuperVec (X ⊗ Y : Even C)) (ForgetEnrichment.to SuperVec (X' ⊗ Y' : Even C)) ≫
      eHomWhiskerRight SuperVec (μF X Y).hom (F.forget.obj (X' ⊗ Y')))
  (hCounit : ∀ X Y : Even D,
    G.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec Y) ≫ F.map (ForgetEnrichment.to SuperVec (G.forget.obj X)) (ForgetEnrichment.to SuperVec (G.forget.obj Y)) ≫
      eHomWhiskerLeft SuperVec (F.forget.obj (G.forget.obj X)) (e Y).hom =
    eHomWhiskerRight SuperVec (e X).hom Y)
  (hμ : ∀ X Y : Even D,
    (μF (G.forget.obj X) (G.forget.obj Y)).hom ≫
      F.forget.map (μG X Y).hom ≫ (e (X ⊗ Y)).hom =
    (e X).hom ⊗ₘ (e Y).hom)

include F hF μF e hM hCounit hμ

/-- A counit compatible with the tensorators reflects enriched tensor
naturality through a fully faithful forward functor. -/
theorem inverse_tensor_natural (X X' Y Y' : Even D) :
    (G.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ G.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (G.forget.obj X) (G.forget.obj X') (G.forget.obj Y) (G.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (G.forget.obj X ⊗ G.forget.obj Y) (μG X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫ G.map (ForgetEnrichment.to SuperVec (X ⊗ Y : Even D)) (ForgetEnrichment.to SuperVec (X' ⊗ Y' : Even D)) ≫
      eHomWhiskerRight SuperVec (μG X Y).hom (G.forget.obj (X' ⊗ Y')) := by
  apply (cancel_mono (superHomIso F hF
    (ForgetEnrichment.to SuperVec (G.forget.obj X ⊗ G.forget.obj Y))
    (ForgetEnrichment.to SuperVec (G.forget.obj (X' ⊗ Y')))).hom).1
  apply (cancel_mono (Iso.eHomCongr SuperVec
    (μF (G.forget.obj X) (G.forget.obj Y)).symm (e (X' ⊗ Y'))).hom).1
  dsimp only [superHomIso, Iso.eHomCongr, Iso.symm_hom, Iso.symm_inv]
  simp only [assoc, ← superFunctor_post_assoc, ← superFunctor_pre_assoc]
  with_unfolding_all rw [eHom_whisker_exchange_assoc]
  simp only [← eHomWhiskerLeft_comp, ← eHomWhiskerRight_comp_assoc]
  erw [← reassoc_of% (hM (G.forget.obj X) (G.forget.obj X')
    (G.forget.obj Y) (G.forget.obj Y'))]
  simp only [← eHomWhiskerLeft_comp, hμ]
  erw [← eHom_whisker_exchange]
  erw [reassoc_of% (hCounit (X ⊗ Y) (X' ⊗ Y'))]
  erw [← eHomWhiskerRight_comp]
  simp only [assoc, hμ]
  rw [ambientTensor_post (F.forget.obj (G.forget.obj X))
    (F.forget.obj (G.forget.obj Y)) (e X').hom (e Y').hom]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [assoc, hCounit]
  exact (ambientTensor_pre (e X).hom (e Y).hom X' Y').symm

end RMod.BrundanEllis.Stacking
