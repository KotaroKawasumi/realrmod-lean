import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! The symmetry of the enriching category interchanges the two factors
of the enriched product compatibly with composition. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
namespace RMod.BrundanEllis.Stacking
variable {V : Type*} [Category* V] [MonoidalCategory V] [SymmetricCategory V]

theorem tensorMu_swap (A B C D : V) :
    tensorμ A B C D ≫ (β_ (A ⊗ C) (B ⊗ D)).hom =
      ((β_ A B).hom ⊗ₘ (β_ C D).hom) ≫ tensorμ B A D C := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding C B, tensorHom_def]

end RMod.BrundanEllis.Stacking
