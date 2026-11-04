import RMod.BrundanEllis.StackingKaroubiEmbeddingComparison
import RMod.BrundanEllis.StackingKaroubiSuperMonoidal

/-! The inclusion of trivial corners preserves the full graded tensor.
Its ordinary tensor comparison is already known to be the ambient identity;
faithful Hom inclusions therefore reflect the enriched comparison equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)]

abbrev embedded (X : Even C) : Even (Karoubi (Even C)) := (embedding C).forget.obj X

@[reassoc] theorem embedding_map_inclusion (X Y : Even C) :
    (embedding C).map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec Y) ≫
      evenInclusion (embedded X) (embedded Y) = 𝟙 (X ⟶[SuperVec] Y) :=
  (restriction_inclusion _ _).trans (original_projector C _ _)

@[reassoc] theorem embedding_mu_post (W : Even (Karoubi (Even C))) (X Y : Even C) :
    eHomWhiskerLeft SuperVec W ((embeddingMonoidal C).μIso X Y).hom ≫
      evenInclusion W (embedded (X ⊗ Y)) = evenInclusion W (embedded X ⊗ embedded Y) := by
  rw [even_whisker_post]
  have h := whisker_post_inclusion (ForgetEnrichment.to SuperVec W)
    ((evenEquivalence (C := C)).functor.map ((embeddingMonoidal C).μIso X Y).hom)
  refine h.trans ?_
  rw [embeddingMonoidal_mu_map]
  change evenInclusion W (embedded X ⊗ embedded Y) ≫
    eHomWhiskerLeft SuperVec (baseObject W) (𝟙 (X ⊗ Y)) = _
  exact (congrArg (fun f => evenInclusion W (embedded X ⊗ embedded Y) ≫ f)
    (eHomWhiskerLeft_id SuperVec (baseObject W) (X ⊗ Y))).trans (Category.comp_id _)

@[reassoc] theorem embedding_mu_pre (X Y : Even C) (W : Even (Karoubi (Even C))) :
    eHomWhiskerRight SuperVec ((embeddingMonoidal C).μIso X Y).hom W ≫
      evenInclusion (embedded X ⊗ embedded Y) W = evenInclusion (embedded (X ⊗ Y)) W := by
  rw [even_whisker_pre]
  have h := whisker_pre_inclusion
    ((evenEquivalence (C := C)).functor.map ((embeddingMonoidal C).μIso X Y).hom)
    (ForgetEnrichment.to SuperVec W)
  refine h.trans ?_
  rw [embeddingMonoidal_mu_map]
  change evenInclusion (embedded (X ⊗ Y)) W ≫
    eHomWhiskerRight SuperVec (𝟙 (X ⊗ Y)) (baseObject W) = _
  rw [eHomWhiskerRight_id]
  exact Category.comp_id _

variable [MonoidalSuperCategory C]

theorem embedding_tensor_natural (X X' Y Y' : Even C) :
    ((embedding C).map X X' ⊗ₘ (embedding C).map Y Y') ≫
      completedTensorMap (embedded X) (embedded X') (embedded Y) (embedded Y') ≫
      eHomWhiskerLeft SuperVec (embedded X ⊗ embedded Y) ((embeddingMonoidal C).μIso X' Y').hom =
    ambientTensor X X' Y Y' ≫ (embedding C).map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec ((embeddingMonoidal C).μIso X Y).hom (embedded (X' ⊗ Y')) := by
  apply (cancel_mono (evenInclusion (embedded X ⊗ embedded Y) (embedded (X' ⊗ Y')))).1
  simp only [assoc, embedding_mu_post, embedding_mu_pre, completedTensorMap_inclusion,
    tensorHom_comp_tensorHom_assoc, embedding_map_inclusion,
    id_tensorHom_id, Category.id_comp, Category.comp_id]
  calc
    _ = (𝟙 (X ⟶[SuperVec] X') ⊗ₘ 𝟙 (Y ⟶[SuperVec] Y')) ≫ ambientTensor X X' Y Y' :=
      congrArg₂ (fun f g => (f ⊗ₘ g) ≫ ambientTensor X X' Y Y')
        (embedding_map_inclusion X X') (embedding_map_inclusion Y Y')
    _ = _ := by rw [id_tensorHom_id, Category.id_comp]

end RMod.BrundanEllis.Stacking.KaroubiSuper
