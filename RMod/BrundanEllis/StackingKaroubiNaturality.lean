import RMod.BrundanEllis.StackingKaroubiTensorMap
import RMod.BrundanEllis.StackingKaroubiStructuralMaps
import RMod.BrundanEllis.StackingProductNaturality

/-! Full Hom naturality on the completion is reflected by the corner
inclusions. Once included, the diagrams are the ambient monoidal diagrams. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalSuperCategory C]
local instance : RMod.MonoidalEnrichedCategory SuperVec C := Bridge.toEnriched C

def completedTensorMap (P P' Q Q' : Even (Karoubi (Even C))) :=
  enrichedTensorMap (completedTensor C) (completedTensor_objects C) P P' Q Q'
def ambientTensor (X X' Y Y' : Even C) :=
  enrichedTensorMap (C := C) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects X X' Y Y'

@[reassoc] theorem completedTensorMap_inclusion (P P' Q Q' : Even (Karoubi (Even C))) :
    completedTensorMap P P' Q Q' ≫ evenInclusion (P ⊗ Q) (P' ⊗ Q') =
      (evenInclusion P P' ⊗ₘ evenInclusion Q Q') ≫
        ambientTensor (baseObject P) (baseObject P') (baseObject Q) (baseObject Q') :=
  completedTensor_aligned_inclusion C P P' Q Q'

theorem completed_associator_naturality (P P' Q Q' R R' : Even (Karoubi (Even C))) :
    (completedTensorMap P P' Q Q' ⊗ₘ 𝟙 (evenHom R R')) ≫
      completedTensorMap (P ⊗ Q) (P' ⊗ Q') R R' ≫
      eHomWhiskerLeft SuperVec ((P ⊗ Q) ⊗ R) (α_ P' Q' R').hom =
    (α_ (evenHom P P') (evenHom Q Q') (evenHom R R')).hom ≫
      (𝟙 (evenHom P P') ⊗ₘ completedTensorMap Q Q' R R') ≫
      completedTensorMap P P' (Q ⊗ R) (Q' ⊗ R') ≫
      eHomWhiskerRight SuperVec (α_ P Q R).hom (P' ⊗ (Q' ⊗ R')) := by
  apply (cancel_mono (evenInclusion ((P ⊗ Q) ⊗ R) (P' ⊗ (Q' ⊗ R')))).1
  simp only [assoc, associator_post, associator_pre,
    completedTensorMap_inclusion_assoc, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, completedTensorMap_inclusion]
  have hl :
      (((evenInclusion P P' ⊗ₘ evenInclusion Q Q') ≫ ambientTensor (baseObject P) (baseObject P')
        (baseObject Q) (baseObject Q')) ⊗ₘ evenInclusion R R') =
      ((evenInclusion P P' ⊗ₘ evenInclusion Q Q') ⊗ₘ evenInclusion R R') ≫
        (ambientTensor (baseObject P) (baseObject P') (baseObject Q) (baseObject Q') ⊗ₘ
          𝟙 (baseObject R ⟶[SuperVec] baseObject R')) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hr :
      (evenInclusion P P' ⊗ₘ ((evenInclusion Q Q' ⊗ₘ evenInclusion R R') ≫
        ambientTensor (baseObject Q) (baseObject Q') (baseObject R) (baseObject R'))) =
      (evenInclusion P P' ⊗ₘ (evenInclusion Q Q' ⊗ₘ evenInclusion R R')) ≫
        (𝟙 (baseObject P ⟶[SuperVec] baseObject P') ⊗ₘ
          ambientTensor (baseObject Q) (baseObject Q') (baseObject R) (baseObject R')) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  rw [hl, hr]
  simp only [assoc]
  rw [← associator_naturality_assoc]
  congr 1
  simpa only [componentTensorMap, ambientTensor, baseObject_tensor, baseObject_unit, baseObject, SHom, ForgetEnrichment.to, ForgetEnrichment.of] using
    RMod.MonoidalEnrichedCategory.associator_naturality (C := C) SuperVec
      (baseObject P) (baseObject P') (baseObject Q) (baseObject Q') (baseObject R) (baseObject R')

/-- The completed tensor unit is the trivial corner of the ambient unit. -/
theorem completed_unit_inclusion :
    eId (C := Karoubi (Even C)) SuperVec
        (ForgetEnrichment.to SuperVec (𝟙_ (Even (Karoubi (Even C))))) ≫
      evenInclusion (𝟙_ (Even (Karoubi (Even C)))) (𝟙_ (Even (Karoubi (Even C)))) =
    eId (C := C) SuperVec (ForgetEnrichment.to SuperVec (𝟙_ (Even C))) := by
  change identity ((𝟙_ (Even C) : Even C) : Karoubi (Even C)) ≫
      inclusion ((𝟙_ (Even C) : Even C) : Karoubi (Even C))
        ((𝟙_ (Even C) : Even C) : Karoubi (Even C)) = _
  rw [identity_inclusion]
  exact eHomEquiv_id SuperVec (𝟙_ (Even C))

theorem completed_left_naturality (P Q : Even (Karoubi (Even C))) :
    (λ_ (evenHom P Q)).inv ≫
      (eId (C := Karoubi (Even C)) SuperVec
          (ForgetEnrichment.to SuperVec (𝟙_ (Even (Karoubi (Even C))))) ⊗ₘ 𝟙 (evenHom P Q)) ≫
      completedTensorMap (𝟙_ _) (𝟙_ _) P Q ≫
      eHomWhiskerLeft SuperVec ((𝟙_ _) ⊗ P) (λ_ Q).hom =
    eHomWhiskerRight SuperVec (λ_ P).hom Q := by
  apply (cancel_mono (evenInclusion ((𝟙_ (Even (Karoubi (Even C)))) ⊗ P) Q)).1
  simp only [assoc, leftUnitor_post, leftUnitor_pre,
    completedTensorMap_inclusion_assoc, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, completed_unit_inclusion]
  rw [leftUnitor_inv_comp_tensorHom_assoc]
  congr 1
  simpa only [componentTensorMap, ambientTensor, baseObject_tensor, baseObject_unit, tensorHom_id, baseObject, SHom, ForgetEnrichment.to, ForgetEnrichment.of] using
    RMod.MonoidalEnrichedCategory.left_naturality (C := C) SuperVec (baseObject P) (baseObject Q)

theorem completed_right_naturality (P Q : Even (Karoubi (Even C))) :
    (ρ_ (evenHom P Q)).inv ≫
      (𝟙 (evenHom P Q) ⊗ₘ eId (C := Karoubi (Even C)) SuperVec
          (ForgetEnrichment.to SuperVec (𝟙_ (Even (Karoubi (Even C)))))) ≫
      completedTensorMap P Q (𝟙_ _) (𝟙_ _) ≫
      eHomWhiskerLeft SuperVec (P ⊗ (𝟙_ _)) (ρ_ Q).hom =
    eHomWhiskerRight SuperVec (ρ_ P).hom Q := by
  apply (cancel_mono (evenInclusion (P ⊗ (𝟙_ (Even (Karoubi (Even C))))) Q)).1
  simp only [assoc, rightUnitor_post, rightUnitor_pre,
    completedTensorMap_inclusion_assoc, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, completed_unit_inclusion]
  rw [rightUnitor_inv_comp_tensorHom_assoc]
  congr 1
  simpa only [componentTensorMap, ambientTensor, baseObject_tensor, baseObject_unit, id_tensorHom, baseObject, SHom, ForgetEnrichment.to, ForgetEnrichment.of] using
    RMod.MonoidalEnrichedCategory.right_naturality (C := C) SuperVec (baseObject P) (baseObject Q)

end RMod.BrundanEllis.Stacking.KaroubiSuper
