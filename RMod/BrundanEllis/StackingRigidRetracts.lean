import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Retract

/-! Retractions are stable under tensor product and chosen right duals.
Thus the self-dual tensor of a summand is a retract of the corresponding
self-dual tensor of its ambient object. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking.Retracts
variable {C : Type} [Category C] [MonoidalCategory C]

def tensor {X X' Y Y' : C} (r : Retract X Y) (s : Retract X' Y') :
    Retract (X ⊗ X') (Y ⊗ Y') where
  i := r.i ⊗ₘ s.i
  r := r.r ⊗ₘ s.r
  retract := by rw [tensorHom_comp_tensorHom, r.retract, s.retract, id_tensorHom_id]

def rightDual {X Y : C} [HasRightDual X] [HasRightDual Y] (r : Retract X Y) :
    Retract (Xᘁ) (Yᘁ) where
  i := rightAdjointMate r.r
  r := rightAdjointMate r.i
  retract := by rw [← comp_rightAdjointMate, r.retract, rightAdjointMate_id]

def selfDual {X Y : C} [HasRightDual X] [HasRightDual Y] (r : Retract X Y) :
    Retract (X ⊗ Xᘁ) (Y ⊗ Yᘁ) := tensor r (rightDual r)

end RMod.BrundanEllis.Stacking.Retracts
