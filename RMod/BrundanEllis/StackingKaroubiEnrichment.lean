import RMod.BrundanEllis.StackingKaroubiComposition

/-! The even idempotent completion as an enriched category. Its Hom inclusion
reflects equality, so associativity and unit laws follow from the ambient laws. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C]

instance inclusion_mono (P Q : Karoubi (Even C)) : Mono (inclusion P Q) where
  right_cancellation f g h := by
    simpa only [assoc, inclusion_restriction, Category.comp_id] using
      congrArg (fun k => k ≫ restriction P Q) h

theorem identity_composition (P Q : Karoubi (Even C)) :
    (λ_ (homObject P Q)).inv ≫ (identity P ⊗ₘ 𝟙 (homObject P Q)) ≫
      composition P P Q = 𝟙 (homObject P Q) := by
  apply (cancel_mono (inclusion P Q)).1
  simp only [assoc, composition_inclusion, Category.id_comp]
  rw [← assoc (identity P ⊗ₘ 𝟙 _), tensorHom_comp_tensorHom,
    identity_inclusion, Category.id_comp]
  calc
    _ = inclusion P Q ≫ eHomWhiskerRight SuperVec P.p Q.X := by
      rw [eHomWhiskerRight, leftUnitor_inv_naturality_assoc]
      simp only [← tensorHom_id, ← id_tensorHom, ← assoc, tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
    _ = _ := inclusion_pre P Q

theorem composition_identity (P Q : Karoubi (Even C)) :
    (ρ_ (homObject P Q)).inv ≫ (𝟙 (homObject P Q) ⊗ₘ identity Q) ≫
      composition P Q Q = 𝟙 (homObject P Q) := by
  apply (cancel_mono (inclusion P Q)).1
  simp only [assoc, composition_inclusion, Category.id_comp]
  rw [← assoc (𝟙 _ ⊗ₘ identity Q), tensorHom_comp_tensorHom,
    identity_inclusion, Category.id_comp]
  calc
    _ = inclusion P Q ≫ eHomWhiskerLeft SuperVec P.X Q.p := by
      rw [eHomWhiskerLeft, rightUnitor_inv_naturality_assoc]
      simp only [← tensorHom_id, ← id_tensorHom, ← assoc, tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
    _ = _ := inclusion_post P Q

theorem composition_associativity (P Q R S : Karoubi (Even C)) :
    (α_ (homObject P Q) (homObject Q R) (homObject R S)).inv ≫
        (composition P Q R ⊗ₘ 𝟙 (homObject R S)) ≫ composition P R S =
      (𝟙 (homObject P Q) ⊗ₘ composition Q R S) ≫ composition P Q S := by
  apply (cancel_mono (inclusion P S)).1
  simp only [assoc, composition_inclusion]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, composition_inclusion]
  have hl :
      (((inclusion P Q ⊗ₘ inclusion Q R) ≫ eComp SuperVec P.X Q.X R.X) ⊗ₘ inclusion R S) =
      ((inclusion P Q ⊗ₘ inclusion Q R) ⊗ₘ inclusion R S) ≫
        (eComp SuperVec P.X Q.X R.X ⊗ₘ 𝟙 (R.X ⟶[SuperVec] S.X)) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hr :
      (inclusion P Q ⊗ₘ ((inclusion Q R ⊗ₘ inclusion R S) ≫ eComp SuperVec Q.X R.X S.X)) =
      (inclusion P Q ⊗ₘ (inclusion Q R ⊗ₘ inclusion R S)) ≫
        (𝟙 (P.X ⟶[SuperVec] Q.X) ⊗ₘ eComp SuperVec Q.X R.X S.X) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  rw [hl, hr]
  simp only [assoc]
  rw [← associator_inv_naturality_assoc]
  simp only [assoc, tensorHom_id, id_tensorHom, e_assoc]

instance enrichment : SuperCategory (Karoubi (Even C)) where
  Hom := homObject
  id := identity
  comp := composition
  id_comp P Q := by simpa only [tensorHom_id] using identity_composition P Q
  comp_id P Q := by simpa only [id_tensorHom] using composition_identity P Q
  assoc P Q R S := by
    simpa only [tensorHom_id, id_tensorHom] using composition_associativity P Q R S

end RMod.BrundanEllis.Stacking.KaroubiSuper
