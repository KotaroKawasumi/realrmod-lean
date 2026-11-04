import RMod.BrundanEllis.Foundation
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-! Full Hom naturality of an enriched functor with respect to even arrows.
These equations allow functors to restrict to idempotent Hom corners. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]

@[reassoc] theorem superFunctor_post (F : SuperFunctor C D)
    (X : Even C) {Y Z : Even C} (f : Y ⟶ Z) :
    F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec Y) ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X) (F.forget.map f) =
    eHomWhiskerLeft SuperVec X f ≫
      F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec Z) := by
  change F.map _ _ ≫ (ρ_ _).inv ≫ _ ◁
      (ForgetEnrichment.homTo SuperVec f ≫ F.map _ _) ≫ eComp SuperVec _ _ _ =
    ((ρ_ _).inv ≫ _ ◁ ForgetEnrichment.homTo SuperVec f ≫ eComp SuperVec _ _ _) ≫ F.map _ _
  rw [rightUnitor_inv_naturality_assoc]
  simp only [assoc, whiskerLeft_comp, ← tensorHom_def_assoc,
    EnrichedFunctor.map_comp, whiskerLeft_comp_tensorHom_assoc, tensorHom_comp_whiskerLeft_assoc]

@[reassoc] theorem superFunctor_pre (F : SuperFunctor C D)
    {X Y : Even C} (f : X ⟶ Y) (Z : Even C) :
    F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Z) ≫
      eHomWhiskerRight SuperVec (F.forget.map f) (F.forget.obj Z) =
    eHomWhiskerRight SuperVec f Z ≫
      F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec Z) := by
  change F.map _ _ ≫ (λ_ _).inv ≫
      (ForgetEnrichment.homTo SuperVec f ≫ F.map _ _) ▷ _ ≫ eComp SuperVec _ _ _ =
    ((λ_ _).inv ≫ ForgetEnrichment.homTo SuperVec f ▷ _ ≫ eComp SuperVec _ _ _) ≫ F.map _ _
  rw [leftUnitor_inv_naturality_assoc]
  simp only [assoc, comp_whiskerRight, ← tensorHom_def'_assoc,
    EnrichedFunctor.map_comp, whiskerRight_comp_tensorHom_assoc, tensorHom_comp_whiskerRight_assoc]

end RMod.BrundanEllis.Stacking
