import RMod.BrundanEllis.StackingEvenNaturality
import Mathlib.CategoryTheory.Enriched.HomCongr

/-! Conjugation by ordinary isomorphisms preserves identity and composition
on entire enriched Hom objects. This is stronger than its evaluation on
even arrows and is the ingredient needed to lift an ordinary quasi-inverse. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {V : Type*} [Category* V] [MonoidalCategory V]
  {C : Type*} [Category* C] [EnrichedOrdinaryCategory V C]

@[reassoc] theorem homCongr_identity {X X' : C} (e : X ≅ X') :
    eId V X ≫ (Iso.eHomCongr V e e).hom = eId V X' := by
  rw [Iso.eHomCongr, ← eHomEquiv_id, ← assoc, even_pre, even_post]
  simp only [Category.comp_id, Iso.inv_hom_id, eHomEquiv_id]

@[reassoc] theorem homCongr_composition {X Y Z X' Y' Z' : C}
    (a : X ≅ X') (b : Y ≅ Y') (c : Z ≅ Z') :
    ((Iso.eHomCongr V a b).hom ⊗ₘ (Iso.eHomCongr V b c).hom) ≫
      eComp V X' Y' Z' = eComp V X Y Z ≫ (Iso.eHomCongr V a c).hom := by
  simp only [Iso.eHomCongr, tensorHom_def, comp_whiskerRight,
    whiskerLeft_comp, assoc]
  rw [← eComp_eHomWhiskerLeft, eHom_whisker_cancel_assoc,
    ← eComp_eHomWhiskerRight_assoc]

end RMod.BrundanEllis.Stacking
