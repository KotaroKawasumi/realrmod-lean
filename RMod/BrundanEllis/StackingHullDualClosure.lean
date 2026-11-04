import RMod.BrundanEllis.StackingHullDuals
import RMod.BrundanEllis.StackingCompletion

/-! The finite fusion hypotheses make every unital tensor-closed hull rigid.
A simple summand of a dual gives, by taking its opposite dual, a retract of
the original object. The intrinsic orbit subgroup then supplies the required
simple summand. Thus dual closure is proved rather than assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
namespace Stacking
variable {C : WeaklyPointedFusionPiSuperCat}

/-- Taking a dual reverses the two maps of a retract. -/
def leftDualRetract {X Y : Even C} (r : Retract X Y) : Retract (ᘁX) (ᘁY) where
  i := ᘁr.r
  r := ᘁr.i
  retract := by
    rw [← comp_leftAdjointMate, r.retract, leftAdjointMate_id]

def rightDualRetract {X Y : Even C} (r : Retract X Y) : Retract (Xᘁ) (Yᘁ) where
  i := r.rᘁ
  r := r.iᘁ
  retract := by
    rw [← comp_rightAdjointMate, r.retract, rightAdjointMate_id]

end Stacking
namespace AddPiHull
variable {C : WeaklyPointedFusionPiSuperCat} {I : Type} {Z : I → Even C}

/-- In a semisimple category the simple retracts detect membership in the hull. -/
theorem of_simple_retracts (X : Even C)
    (h : ∀ S : Even C, Simple S → Nonempty (Retract S X) → AddPiHull C Z S) :
    AddPiHull C Z X := by
  obtain ⟨n, S, hS, ⟨e⟩⟩ := FusionPiSuperCategory.semisimple (C := C) X
  apply (iso_iff e).mpr
  apply finite_biproduct S
  intro i
  apply h (S i) (hS i)
  exact ⟨{
    i := biproduct.ι S i ≫ e.inv
    r := e.hom ≫ biproduct.π S i
    retract := by simp [Category.assoc] }⟩

variable [ObjectProperty.IsMonoidal (AddPiHull C Z)]

attribute [-instance] hasRightDualLeftDual hasLeftDualRightDual in
/-- Tensor closure already forces closure under the chosen right dual. -/
theorem right_dual_mem {X : Even C} (hX : AddPiHull C Z X) : AddPiHull C Z (Xᘁ) := by
  apply of_simple_retracts
  rintro S hS ⟨r⟩
  letI := hS
  let e : (ᘁ(Xᘁ) : Even C) ≅ X := leftDualIso
    (inferInstance : ExactPairing (ᘁ(Xᘁ)) (Xᘁ))
    (inferInstance : ExactPairing X (Xᘁ))
  have hL : AddPiHull C Z (ᘁS) :=
    of_retract ((Stacking.leftDualRetract r).trans (Retract.ofIso e)) hX
  letI : Simple (ᘁS) := Stacking.pairing_left_simple C (ᘁS) S
  exact Stacking.pairing_right_mem C Z (ᘁS) S hL

attribute [-instance] hasRightDualLeftDual hasLeftDualRightDual in
/-- The argument with the two dual conventions interchanged gives the left dual. -/
theorem left_dual_mem {X : Even C} (hX : AddPiHull C Z X) : AddPiHull C Z (ᘁX) := by
  apply of_simple_retracts
  rintro S hS ⟨r⟩
  letI := hS
  let e : ((ᘁX)ᘁ : Even C) ≅ X := rightDualIso
    (inferInstance : ExactPairing (ᘁX) ((ᘁX)ᘁ))
    (inferInstance : ExactPairing (ᘁX) X)
  have hR : AddPiHull C Z (Sᘁ) :=
    of_retract ((Stacking.rightDualRetract r).trans (Retract.ofIso e)) hX
  letI : Simple (Sᘁ) := Stacking.pairing_right_simple C S (Sᘁ)
  exact Stacking.pairing_left_mem C Z S (Sᘁ) hR

end AddPiHull

/-- A unital tensor-closed completion is itself a weakly pointed fusion
Π-supercategory; dual closure is supplied by the preceding theorems. -/
def tensorClosedCompletion (C : WeaklyPointedFusionPiSuperCat) {I : Type}
    (Z : I → Even C) [ObjectProperty.IsMonoidal (AddPiHull C Z)] :
    WeaklyPointedFusionPiSuperCat :=
  hullFusionCategory C Z (fun X => AddPiHull.left_dual_mem X.property)
    (fun X => AddPiHull.right_dual_mem X.property)

end RMod.BrundanEllis
