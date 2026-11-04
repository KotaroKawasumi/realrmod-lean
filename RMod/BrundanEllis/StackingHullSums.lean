import RMod.BrundanEllis.StackingHull

/-! Finite sums in the diagonal completion.  Flattening the finite index
sets shows that the single-stage completion predicate is already additive. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.AddPiHull
variable {C : WeaklyPointedFusionPiSuperCat} {I : Type} {Z : I → Even C}

/-- A finite index type can be replaced by Fin without changing the hull. -/
theorem of_finite_family {J : Type} [Fintype J] (i : J → I) (p : J → Bool)
    {X : Even C} (r : Retract X (⨁ fun j =>
      if p j then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z (i j) else Z (i j))) :
    AddPiHull C Z X := by
  classical
  let e := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, (fun j => i (e j)), (fun j => p (e j)), ?_⟩
  exact ⟨r.trans (Retract.ofIso (biproduct.whiskerEquiv e (fun _ => Iso.refl _)).symm)⟩

/-- Retractions of each summand assemble into a retraction of the sum. -/
private def sumRetract {J : Type} [Fintype J] {X Y : J → Even C}
    (r : ∀ j, Retract (X j) (Y j)) : Retract (⨁ X) (⨁ Y) where
  i := biproduct.map (fun j => (r j).i)
  r := biproduct.map (fun j => (r j).r)
  retract := by ext j; simp

/-- The completion is closed under arbitrary finite biproducts. -/
theorem finite_biproduct {J : Type} [Fintype J] (X : J → Even C)
    (h : ∀ j, AddPiHull C Z (X j)) : AddPiHull C Z (⨁ X) := by
  classical
  choose n i p hr using h
  let family := fun j (k : Fin (n j)) =>
    if p j k then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z (i j k)
      else Z (i j k)
  let r : Retract (⨁ X) (⨁ fun j => ⨁ family j) :=
    sumRetract (fun j => (hr j).some)
  apply of_finite_family (fun q : Σ j, Fin (n j) => i q.1 q.2)
    (fun q => p q.1 q.2)
  exact r.trans (Retract.ofIso (biproductBiproductIso (fun j => Fin (n j)) family))

end RMod.BrundanEllis.AddPiHull
