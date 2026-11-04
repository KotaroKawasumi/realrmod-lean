import RMod.BrundanEllis.StackingKaroubiMonoidal
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! A dual idempotent is the mate of the original idempotent. Evaluation
and coevaluation restrict to these two corners. The equations below remove
one redundant projector using the mate identities. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiTensor
variable {C : Type} [Category C] [MonoidalCategory C] [RightRigidCategory C]

def rightDualObject (P : Karoubi C) : Karoubi C where
  X := P.Xᘁ
  p := P.pᘁ
  idem := by rw [← comp_rightAdjointMate, P.idem]

def rightCoevaluation (P : Karoubi C) : 𝟙_ (Karoubi C) ⟶ P ⊗ rightDualObject P where
  f := η_ P.X P.Xᘁ ≫ (P.p ⊗ₘ P.pᘁ)
  comm := by
    change (𝟙 _) ≫ (η_ P.X P.Xᘁ ≫ (P.p ⊗ₘ P.pᘁ)) ≫ (P.p ⊗ₘ P.pᘁ) = _
    rw [Category.id_comp, assoc, tensorHom_comp_tensorHom, P.idem,
      ← comp_rightAdjointMate, P.idem]
    rfl

def rightEvaluation (P : Karoubi C) : rightDualObject P ⊗ P ⟶ 𝟙_ (Karoubi C) where
  f := (P.pᘁ ⊗ₘ P.p) ≫ ε_ P.X P.Xᘁ
  comm := by
    change (P.pᘁ ⊗ₘ P.p) ≫ ((P.pᘁ ⊗ₘ P.p) ≫ ε_ P.X P.Xᘁ) ≫ 𝟙 _ = _
    rw [Category.comp_id, ← assoc, tensorHom_comp_tensorHom, P.idem,
      ← comp_rightAdjointMate, P.idem]
    rfl

theorem rightCoevaluation_f (P : Karoubi C) :
    (rightCoevaluation P).f = η_ P.X P.Xᘁ ≫ P.p ▷ P.Xᘁ := by
  change η_ P.X P.Xᘁ ≫ (P.p ⊗ₘ P.pᘁ) = _
  rw [tensorHom_def', ← assoc, coevaluation_comp_rightAdjointMate,
    assoc, ← comp_whiskerRight, P.idem]

theorem rightEvaluation_f (P : Karoubi C) :
    (rightEvaluation P).f = P.Xᘁ ◁ P.p ≫ ε_ P.X P.Xᘁ := by
  change (P.pᘁ ⊗ₘ P.p) ≫ ε_ P.X P.Xᘁ = _
  rw [tensorHom_def', assoc, rightAdjointMate_comp_evaluation,
    ← assoc, ← whiskerLeft_comp, P.idem]

end RMod.BrundanEllis.Stacking.KaroubiTensor
