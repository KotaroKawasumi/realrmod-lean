import RMod.BrundanEllis.StackingKaroubiDualObjects
import RMod.BrundanEllis.StackingProjectedSnake

/-! Right duals survive idempotent completion. The two snake equations
are the original equations sandwiched between the corresponding projectors;
no rigidity assumption on the completion is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiTensor
variable {C : Type} [Category C] [MonoidalCategory C]

theorem comp_associator_hom_f {W P Q R : Karoubi C} (f : W ⟶ (P ⊗ Q) ⊗ R) :
    (f ≫ (α_ P Q R).hom).f = f.f ≫ (α_ P.X Q.X R.X).hom := by
  change f.f ≫ (((P ⊗ Q) ⊗ R).p ≫ (α_ P.X Q.X R.X).hom) = _
  rw [← assoc, Karoubi.comp_p]

theorem associator_inv_comp_f {P Q R W : Karoubi C} (f : (P ⊗ Q) ⊗ R ⟶ W) :
    ((α_ P Q R).inv ≫ f).f = (α_ P.X Q.X R.X).inv ≫ f.f := by
  change ((α_ P.X Q.X R.X).inv ≫ ((P ⊗ Q) ⊗ R).p) ≫ f.f = _
  rw [assoc, Karoubi.p_comp]

variable [RightRigidCategory C]

theorem rightCoevaluation_f' (P : Karoubi C) :
    (rightCoevaluation P).f = η_ P.X P.Xᘁ ≫ P.X ◁ P.pᘁ := by
  rw [rightCoevaluation_f, coevaluation_comp_rightAdjointMate]

theorem rightEvaluation_f' (P : Karoubi C) :
    (rightEvaluation P).f = P.pᘁ ▷ P.X ≫ ε_ P.X P.Xᘁ := by
  rw [rightEvaluation_f, rightAdjointMate_comp_evaluation]

theorem right_forward_snake (P : Karoubi C) :
    rightCoevaluation P ▷ P ≫ (α_ P (rightDualObject P) P).hom ≫ P ◁ rightEvaluation P =
      (λ_ P).hom ≫ (ρ_ P).inv := by
  rw [← assoc]
  apply Karoubi.hom_ext
  change ((rightCoevaluation P ▷ P) ≫ (α_ P (rightDualObject P) P).hom).f ≫
    (P ◁ rightEvaluation P).f = _
  rw [comp_associator_hom_f, whiskerRight_f, whiskerLeft_f,
    rightCoevaluation_f, rightEvaluation_f]
  rw [assoc]
  change ((η_ P.X P.Xᘁ ≫ P.p ▷ P.Xᘁ) ⊗ₘ P.p) ≫ (α_ P.X P.Xᘁ P.X).hom ≫
      (P.p ⊗ₘ (P.Xᘁ ◁ P.p ≫ ε_ P.X P.Xᘁ)) =
    ((𝟙 (𝟙_ C) ⊗ₘ P.p) ≫ (λ_ P.X).hom) ≫ (ρ_ P.X).inv ≫ (P.p ⊗ₘ 𝟙 (𝟙_ C))
  rw [projected_forward_snake P.p P.idem]
  simp only [tensorHom_id, id_tensorHom, assoc]
  rw [ExactPairing.evaluation_coevaluation_assoc]

theorem right_backward_snake (P : Karoubi C) :
    rightDualObject P ◁ rightCoevaluation P ≫ (α_ (rightDualObject P) P (rightDualObject P)).inv ≫
      rightEvaluation P ▷ rightDualObject P =
      (ρ_ (rightDualObject P)).hom ≫ (λ_ (rightDualObject P)).inv := by
  apply Karoubi.hom_ext
  change (rightDualObject P ◁ rightCoevaluation P).f ≫
    ((α_ (rightDualObject P) P (rightDualObject P)).inv ≫
      rightEvaluation P ▷ rightDualObject P).f = _
  rw [associator_inv_comp_f, whiskerLeft_f, whiskerRight_f,
    rightCoevaluation_f', rightEvaluation_f']
  change (P.pᘁ ⊗ₘ (η_ P.X P.Xᘁ ≫ P.X ◁ P.pᘁ)) ≫ (α_ P.Xᘁ P.X P.Xᘁ).inv ≫
      ((P.pᘁ ▷ P.X ≫ ε_ P.X P.Xᘁ) ⊗ₘ P.pᘁ) =
    ((P.pᘁ ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ P.Xᘁ).hom) ≫ (λ_ P.Xᘁ).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ P.pᘁ)
  rw [projected_backward_snake (rightAdjointMate P.p) (rightDualObject P).idem]
  simp only [tensorHom_id, id_tensorHom, assoc]
  rw [ExactPairing.coevaluation_evaluation_assoc]

instance rightExactPairing (P : Karoubi C) : ExactPairing P (rightDualObject P) where
  coevaluation' := rightCoevaluation P
  evaluation' := rightEvaluation P
  coevaluation_evaluation' := right_backward_snake P
  evaluation_coevaluation' := right_forward_snake P

instance rightRigid : RightRigidCategory (Karoubi C) where
  rightDual P := { rightDual := rightDualObject P }

end RMod.BrundanEllis.Stacking.KaroubiTensor
