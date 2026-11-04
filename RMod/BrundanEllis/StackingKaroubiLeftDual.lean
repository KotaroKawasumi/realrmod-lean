import RMod.BrundanEllis.StackingKaroubiLeftDualObjects
import RMod.BrundanEllis.StackingKaroubiRightDual

/-! The left mate construction satisfies both snake identities as well.
Together with right duals, this equips the ordinary completion with rigidity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiTensor
variable {C : Type} [Category C] [MonoidalCategory C] [LeftRigidCategory C]

theorem left_forward_snake (P : Karoubi C) :
    leftCoevaluation P ▷ leftDualObject P ≫ (α_ (leftDualObject P) P (leftDualObject P)).hom ≫
      leftDualObject P ◁ leftEvaluation P =
      (λ_ (leftDualObject P)).hom ≫ (ρ_ (leftDualObject P)).inv := by
  rw [← assoc]
  apply Karoubi.hom_ext
  change ((leftCoevaluation P ▷ leftDualObject P) ≫
    (α_ (leftDualObject P) P (leftDualObject P)).hom).f ≫
    (leftDualObject P ◁ leftEvaluation P).f = _
  rw [comp_associator_hom_f, whiskerRight_f, whiskerLeft_f,
    leftCoevaluation_f', leftEvaluation_f']
  rw [assoc]
  change ((η_ (HasLeftDual.leftDual P.X) P.X ≫ (ᘁP.p) ▷ P.X) ⊗ₘ (ᘁP.p)) ≫ (α_ (HasLeftDual.leftDual P.X) P.X (HasLeftDual.leftDual P.X)).hom ≫
      ((ᘁP.p) ⊗ₘ (P.X ◁ (ᘁP.p) ≫ ε_ (HasLeftDual.leftDual P.X) P.X)) =
    ((𝟙 (𝟙_ C) ⊗ₘ (ᘁP.p)) ≫ (λ_ (HasLeftDual.leftDual P.X)).hom) ≫ (ρ_ (HasLeftDual.leftDual P.X)).inv ≫ ((ᘁP.p) ⊗ₘ 𝟙 (𝟙_ C))
  rw [projected_forward_snake (leftAdjointMate P.p) (leftDualObject P).idem]
  simp only [tensorHom_id, id_tensorHom, assoc]
  rw [ExactPairing.evaluation_coevaluation_assoc]

theorem left_backward_snake (P : Karoubi C) :
    P ◁ leftCoevaluation P ≫ (α_ P (leftDualObject P) P).inv ≫ leftEvaluation P ▷ P =
      (ρ_ P).hom ≫ (λ_ P).inv := by
  apply Karoubi.hom_ext
  change (P ◁ leftCoevaluation P).f ≫
    ((α_ P (leftDualObject P) P).inv ≫ leftEvaluation P ▷ P).f = _
  rw [associator_inv_comp_f, whiskerLeft_f, whiskerRight_f,
    leftCoevaluation_f, leftEvaluation_f]
  change (P.p ⊗ₘ (η_ (HasLeftDual.leftDual P.X) P.X ≫ (HasLeftDual.leftDual P.X) ◁ P.p)) ≫ (α_ P.X (HasLeftDual.leftDual P.X) P.X).inv ≫
      ((P.p ▷ (HasLeftDual.leftDual P.X) ≫ ε_ (HasLeftDual.leftDual P.X) P.X) ⊗ₘ P.p) =
    ((P.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ P.X).hom) ≫ (λ_ P.X).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ P.p)
  rw [projected_backward_snake P.p P.idem]
  simp only [tensorHom_id, id_tensorHom, assoc]
  rw [ExactPairing.coevaluation_evaluation_assoc]

instance leftExactPairing (P : Karoubi C) : ExactPairing (leftDualObject P) P where
  coevaluation' := leftCoevaluation P
  evaluation' := leftEvaluation P
  coevaluation_evaluation' := left_backward_snake P
  evaluation_coevaluation' := left_forward_snake P

instance leftRigid : LeftRigidCategory (Karoubi C) where
  leftDual P := { leftDual := leftDualObject P }

instance rigid [RightRigidCategory C] : RigidCategory (Karoubi C) where

end RMod.BrundanEllis.Stacking.KaroubiTensor
