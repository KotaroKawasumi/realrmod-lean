import RMod.BrundanEllis.Classification

/-! The completion predicate fixed by Challenge and its elementary closure
properties.  Retractions here are in the even category, as required by the
completion of the diagonal component. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis

/-! Finite sums, parity shifts and even retracts specify the completion. -/
def AddPiHull (C : WeaklyPointedFusionPiSuperCat) {I : Type}
    (Z : I → Even C) (X : Even C) : Prop :=
  ∃ (n : ℕ) (i : Fin n → I) (p : Fin n → Bool), Nonempty (Retract X
    (⨁ fun j => if p j then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z (i j)
      else Z (i j)))

namespace AddPiHull
variable {C : WeaklyPointedFusionPiSuperCat} {I : Type} {Z : I → Even C}

/-- Every generating object lies in its completion. -/
theorem generator (i : I) : AddPiHull C Z (Z i) := by
  refine ⟨1, (fun _ => i), (fun _ => false), ?_⟩
  exact ⟨Retract.ofIso (biproductUniqueIso (fun _ : Fin 1 => Z i)).symm⟩

/-- The specified parity shifts are also generators. -/
theorem parityGenerator (i : I) :
    AddPiHull C Z (evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z i) := by
  refine ⟨1, (fun _ => i), (fun _ => true), ?_⟩
  exact ⟨Retract.ofIso (biproductUniqueIso (fun _ : Fin 1 =>
    evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z i)).symm⟩

/-- Taking another even retract stays in the same completion. -/
theorem of_retract {X Y : Even C} (r : Retract X Y) (h : AddPiHull C Z Y) :
    AddPiHull C Z X := by
  obtain ⟨n, i, p, ⟨q⟩⟩ := h
  exact ⟨n, i, p, ⟨r.trans q⟩⟩

/-- Membership depends only on the even isomorphism class. -/
theorem iso_iff {X Y : Even C} (e : X ≅ Y) :
    AddPiHull C Z X ↔ AddPiHull C Z Y :=
  ⟨of_retract (Retract.ofIso e.symm), of_retract (Retract.ofIso e)⟩

end AddPiHull
end RMod.BrundanEllis
