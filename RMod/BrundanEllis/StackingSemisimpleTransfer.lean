import RMod.BrundanEllis.Surface
import Mathlib.CategoryTheory.Abelian.Transfer

/-! Ordinary categorical equivalences preserve simple objects and finite
semisimple decompositions. These statements do not assume compatibility
with tensor products and are used before the monoidal model comparison. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts preservesBiproduct_of_preservesProduct
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [Category C] [Category D]

/-- Simplicity reflects along an equivalence because zero maps and monos do. -/
theorem simple_reflects_equivalence [HasZeroMorphisms C] [HasZeroMorphisms D] (E : C ≌ D) (X : C) [Simple (E.functor.obj X)] :
    Simple X := by
  refine ⟨fun f _ => ?_⟩
  exact (isIso_iff_of_reflects_iso f E.functor).symm.trans
    ((Simple.mono_isIso_iff_nonzero (E.functor.map f)).trans
      (not_congr (Functor.map_eq_zero_iff E.functor)))

variable [Abelian C] [Abelian D]

/-- Map the target decomposition back, using the unit and biproduct comparison. -/
theorem semisimple_of_equivalence (E : C ≌ D)
    (h : ∀ X : D, ∃ (n : ℕ) (S : Fin n → D),
      (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)) (X : C) :
    ∃ (n : ℕ) (S : Fin n → C), (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S) := by
  obtain ⟨n, S, hS, ⟨e⟩⟩ := h (E.functor.obj X)
  refine ⟨n, fun i => E.inverse.obj (S i), fun i => ?_, ?_⟩
  · letI : Simple (S i) := hS i
    letI : Simple (E.functor.obj (E.inverse.obj (S i))) := Simple.of_iso (Y := S i) (E.counitIso.app (S i))
    exact simple_reflects_equivalence E _
  · exact ⟨E.unitIso.app X ≪≫ E.inverse.mapIso e ≪≫ E.inverse.mapBiproduct S⟩

end RMod.BrundanEllis.Stacking
