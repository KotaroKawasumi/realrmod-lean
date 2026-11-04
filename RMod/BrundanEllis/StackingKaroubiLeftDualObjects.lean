import RMod.BrundanEllis.StackingKaroubiMonoidal
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! Left dual corners use left mates. Their evaluation and coevaluation
are the ambient maps restricted by the two idempotents. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiTensor
variable {C : Type} [Category C] [MonoidalCategory C] [LeftRigidCategory C]

def leftDualObject (P : Karoubi C) : Karoubi C where
  X := HasLeftDual.leftDual P.X
  p := ᘁP.p
  idem := by rw [← comp_leftAdjointMate, P.idem]

def leftCoevaluation (P : Karoubi C) : 𝟙_ (Karoubi C) ⟶ leftDualObject P ⊗ P where
  f := η_ (HasLeftDual.leftDual P.X) P.X ≫ ((ᘁP.p) ⊗ₘ P.p)
  comm := by
    change (𝟙 _) ≫ (η_ (HasLeftDual.leftDual P.X) P.X ≫ ((ᘁP.p) ⊗ₘ P.p)) ≫ ((ᘁP.p) ⊗ₘ P.p) = _
    rw [Category.id_comp, assoc, tensorHom_comp_tensorHom, P.idem,
      ← comp_leftAdjointMate, P.idem]
    rfl

def leftEvaluation (P : Karoubi C) : P ⊗ leftDualObject P ⟶ 𝟙_ (Karoubi C) where
  f := (P.p ⊗ₘ (ᘁP.p)) ≫ ε_ (HasLeftDual.leftDual P.X) P.X
  comm := by
    change (P.p ⊗ₘ (ᘁP.p)) ≫ ((P.p ⊗ₘ (ᘁP.p)) ≫ ε_ (HasLeftDual.leftDual P.X) P.X) ≫ 𝟙 _ = _
    rw [Category.comp_id, ← assoc, tensorHom_comp_tensorHom, P.idem,
      ← comp_leftAdjointMate, P.idem]
    rfl

theorem leftCoevaluation_f (P : Karoubi C) :
    (leftCoevaluation P).f = η_ (HasLeftDual.leftDual P.X) P.X ≫ (HasLeftDual.leftDual P.X) ◁ P.p := by
  change η_ (HasLeftDual.leftDual P.X) P.X ≫ ((ᘁP.p) ⊗ₘ P.p) = _
  rw [tensorHom_def, ← assoc, coevaluation_comp_leftAdjointMate,
    assoc, ← whiskerLeft_comp, P.idem]

theorem leftEvaluation_f (P : Karoubi C) :
    (leftEvaluation P).f = P.p ▷ (HasLeftDual.leftDual P.X) ≫ ε_ (HasLeftDual.leftDual P.X) P.X := by
  change (P.p ⊗ₘ (ᘁP.p)) ≫ ε_ (HasLeftDual.leftDual P.X) P.X = _
  rw [tensorHom_def, assoc, leftAdjointMate_comp_evaluation,
    ← assoc, ← comp_whiskerRight, P.idem]

theorem leftCoevaluation_f' (P : Karoubi C) :
    (leftCoevaluation P).f = η_ (HasLeftDual.leftDual P.X) P.X ≫ (ᘁP.p) ▷ P.X := by
  rw [leftCoevaluation_f, coevaluation_comp_leftAdjointMate]

theorem leftEvaluation_f' (P : Karoubi C) :
    (leftEvaluation P).f = P.X ◁ (ᘁP.p) ≫ ε_ (HasLeftDual.leftDual P.X) P.X := by
  rw [leftEvaluation_f, leftAdjointMate_comp_evaluation]

end RMod.BrundanEllis.Stacking.KaroubiTensor
