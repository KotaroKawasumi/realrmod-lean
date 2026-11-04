import RMod.BrundanEllis.StackingKaroubiFunctorComparison
import RMod.BrundanEllis.StackingKaroubiSuperMonoidal

/-! Tensor compatibility in every homogeneous degree passes to idempotent
corners. Including the corner Hom spaces turns the required square back
into the given square for the original enriched functor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  (F : SuperFunctor C D) (M : F.forget.CoreMonoidal)

@[reassoc] theorem functor_mu_post (W : Even (Karoubi (Even D)))
    (P Q : Even (Karoubi (Even C))) :
    eHomWhiskerLeft SuperVec W ((functorMonoidal F M).μIso P Q).hom ≫
      evenInclusion W ((functor F).forget.obj (P ⊗ Q)) =
      evenInclusion W ((functor F).forget.obj P ⊗ (functor F).forget.obj Q) ≫
        eHomWhiskerLeft SuperVec (baseObject W) (M.μIso (baseObject P) (baseObject Q)).hom := by
  rw [even_whisker_post, functorMonoidal_mu_cut]
  exact cut_post_inclusion _ _ _

@[reassoc] theorem functor_mu_pre (P Q : Even (Karoubi (Even C)))
    (W : Even (Karoubi (Even D))) :
    eHomWhiskerRight SuperVec ((functorMonoidal F M).μIso P Q).hom W ≫
      evenInclusion ((functor F).forget.obj P ⊗ (functor F).forget.obj Q) W =
      evenInclusion ((functor F).forget.obj (P ⊗ Q)) W ≫
        eHomWhiskerRight SuperVec (M.μIso (baseObject P) (baseObject Q)).hom (baseObject W) := by
  rw [even_whisker_pre, functorMonoidal_mu_cut]
  exact cut_pre_inclusion _ _ _

@[reassoc] theorem functor_map_inclusion (P Q : Even (Karoubi (Even C))) :
    (functor F).map (ForgetEnrichment.to SuperVec P) (ForgetEnrichment.to SuperVec Q) ≫
      evenInclusion ((functor F).forget.obj P) ((functor F).forget.obj Q) =
      evenInclusion P Q ≫ F.map (ForgetEnrichment.to SuperVec (baseObject P))
        (ForgetEnrichment.to SuperVec (baseObject Q)) :=
  mapHom_inclusion F _ _

variable [MonoidalSuperCategory C] [MonoidalSuperCategory D]

/-- All-degree tensor naturality of the actual completed functor. -/
theorem functor_tensor_natural
    (h : ∀ X X' Y Y' : Even C,
      (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
      ambientTensor X X' Y Y' ≫ F.map (ForgetEnrichment.to SuperVec (X ⊗ Y))
        (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')))
    (P P' Q Q' : Even (Karoubi (Even C))) :
    ((functor F).map (ForgetEnrichment.to SuperVec P) (ForgetEnrichment.to SuperVec P') ⊗ₘ (functor F).map (ForgetEnrichment.to SuperVec Q) (ForgetEnrichment.to SuperVec Q')) ≫
      completedTensorMap ((functor F).forget.obj P) ((functor F).forget.obj P')
        ((functor F).forget.obj Q) ((functor F).forget.obj Q') ≫
      eHomWhiskerLeft SuperVec ((functor F).forget.obj P ⊗ (functor F).forget.obj Q)
        ((functorMonoidal F M).μIso P' Q').hom =
    completedTensorMap P P' Q Q' ≫ (functor F).map (ForgetEnrichment.to SuperVec (P ⊗ Q)) (ForgetEnrichment.to SuperVec (P' ⊗ Q')) ≫
      eHomWhiskerRight SuperVec ((functorMonoidal F M).μIso P Q).hom
        ((functor F).forget.obj (P' ⊗ Q')) := by
  apply (cancel_mono (evenInclusion
    ((functor F).forget.obj P ⊗ (functor F).forget.obj Q)
    ((functor F).forget.obj (P' ⊗ Q')))).1
  simp only [Category.assoc, functor_mu_post, functor_mu_pre,
    completedTensorMap_inclusion_assoc, functor_map_inclusion_assoc]
  rw [tensorHom_comp_tensorHom_assoc, functor_map_inclusion, functor_map_inclusion,
    ← tensorHom_comp_tensorHom_assoc]
  exact congrArg (fun k => (evenInclusion P P' ⊗ₘ evenInclusion Q Q') ≫ k)
    (h (baseObject P) (baseObject P') (baseObject Q) (baseObject Q'))

end RMod.BrundanEllis.Stacking.KaroubiSuper
