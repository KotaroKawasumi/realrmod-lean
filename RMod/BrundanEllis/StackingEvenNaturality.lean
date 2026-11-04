import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-! Evaluating full Hom-object naturality at an even morphism gives the
ordinary naturality square. The identities are independent of super vector
spaces and apply to any enriched ordinary category. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {V : Type*} [Category* V] [MonoidalCategory V]
  {C : Type*} [Category* C] [EnrichedOrdinaryCategory V C]

@[reassoc] theorem even_post {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V f ≫ eHomWhiskerLeft V X g = eHomEquiv V (f ≫ g) := by
  rw [eHomWhiskerLeft, rightUnitor_inv_naturality_assoc, eHomEquiv_comp]
  simp only [tensorHom_def]
  monoidal

@[reassoc] theorem even_pre {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V g ≫ eHomWhiskerRight V f Z = eHomEquiv V (f ≫ g) := by
  rw [eHomWhiskerRight, leftUnitor_inv_naturality_assoc, eHomEquiv_comp]
  simp only [tensorHom_def', assoc]

end RMod.BrundanEllis.Stacking
