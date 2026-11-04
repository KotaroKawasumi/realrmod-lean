import RMod.BrundanEllis.StackingSemisimpleRetracts

/-! Finite additive spans of a specified family, without assuming that the
ambient category is weakly pointed. A span of simple objects is closed
under retracts in a finite semisimple category. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace RMod.BrundanEllis.Stacking
variable {C : Type} [Category C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
  {I : Type} (Z : I → C)

def FiniteSpan (X : C) : Prop :=
  ∃ (n : ℕ) (i : Fin n → I), Nonempty (X ≅ ⨁ fun j => Z (i j))

namespace FiniteSpan
variable {Z}

theorem generator (i : I) : FiniteSpan Z (Z i) :=
  ⟨1, fun _ => i, ⟨(biproductUniqueIso (fun _ : Fin 1 => Z i)).symm⟩⟩

theorem of_iso {X Y : C} (e : X ≅ Y) (h : FiniteSpan Z Y) : FiniteSpan Z X := by
  obtain ⟨n, i, ⟨d⟩⟩ := h
  exact ⟨n, i, ⟨e ≪≫ d⟩⟩

theorem of_finite_family {J : Type} [Fintype J] (i : J → I) :
    FiniteSpan Z (⨁ fun j => Z (i j)) := by
  let e := (Fintype.equivFin J).symm
  exact ⟨Fintype.card J, i ∘ e,
    ⟨(biproduct.whiskerEquiv e (fun _ => Iso.refl _)).symm⟩⟩

theorem finite_biproduct {J : Type} [Fintype J] (X : J → C)
    (h : ∀ j, FiniteSpan Z (X j)) : FiniteSpan Z (⨁ X) := by
  classical
  choose n i h using h
  let e j := (h j).some
  apply of_iso (biproduct.mapIso e ≪≫ biproductBiproductIso (fun j => Fin (n j))
    (fun j k => Z (i j k)))
  exact of_finite_family (fun q : Σ j, Fin (n j) => i q.1 q.2)

end FiniteSpan
end RMod.BrundanEllis.Stacking
