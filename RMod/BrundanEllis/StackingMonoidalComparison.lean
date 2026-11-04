import RMod.BrundanEllis.StackingKaroubiNaturality
import RMod.BrundanEllis.StackingHomEquationTotal
import RMod.BrundanEllis.StackingSuperequivalence

/-! Evaluate enriched tensor naturality on arbitrary total morphisms and
use ordinary essential surjectivity to obtain the chosen inverse objects. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [MonoidalSuperCategory C] [MonoidalSuperCategory D]
  (F : SuperFunctor C D) (M : F.forget.CoreMonoidal)

/-- Evaluate a tensorator square on the full convolution point, so its
Hom-object naturality applies to arbitrary inhomogeneous morphisms. -/
theorem tensor_naturality_total
    (h : ∀ X X' Y Y' : Even C,
      (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
      KaroubiSuper.ambientTensor X X' Y Y' ≫ F.map (ForgetEnrichment.to SuperVec (X ⊗ Y))
        (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')))
    {X X' Y Y' : Even C} (f : THom C X X') (g : THom C Y Y') :
    tComp D (tTensor (C := D) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
      (tMap F f) (tMap F g)) (evenPoint (M.μIso X' Y').hom) =
    tComp D (evenPoint (M.μIso X Y).hom)
      (tMap F (tTensor (C := C) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects f g)) := by
  let L := (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
    F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
    KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y')
  let R := KaroubiSuper.ambientTensor X X' Y Y' ≫
    F.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y'))
  have hn := homEquation_total (D := D)
    (A := F.forget.obj X ⊗ F.forget.obj Y) (B := F.forget.obj X' ⊗ F.forget.obj Y')
    (A' := F.forget.obj (X ⊗ Y)) (B' := F.forget.obj (X' ⊗ Y')) L R
    (M.μIso X Y).hom (M.μIso X' Y').hom
    (by simpa only [L, R, Category.assoc] using h X X' Y Y')
    (RMod.Regression.tensorPoint f g)
  have hl : (fun a => L a (RMod.Regression.tensorPoint f g a)) =
      tTensor (C := D) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        (tMap F f) (tMap F g) := by
    funext a
    change KaroubiSuper.ambientTensor _ _ _ _ a
      ((F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) a
        (RMod.Regression.tensorPoint f g a)) = _
    rw [congrFun (RMod.Regression.tensorPoint_map
      (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X'))
      (F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) f g) a]
    rfl
  rw [hl] at hn
  exact hn

/-- Full graded faithfulness and an ordinary equivalence provide the
representatives needed for the actual monoidal superequivalence. -/
def monoidalSuperequivalenceOfFullyFaithful
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a)) [F.forget.IsEquivalence]
    (hM : ∀ {X X' Y Y' : Even C} (f : THom C X X') (g : THom C Y Y'),
      tComp D (tTensor (C := D) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        (tMap F f) (tMap F g)) (evenPoint (M.μIso X' Y').hom) =
      tComp D (evenPoint (M.μIso X Y).hom)
        (tMap F (tTensor (C := C) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects f g))) :
    MonoidalSuperequivalence C D :=
  monoidalSuperequivalenceOfComparison F hF
    (fun X => ForgetEnrichment.to SuperVec (F.forget.asEquivalence.inverse.obj (evenObj D X)))
    (fun X => F.forget.asEquivalence.counitIso.app (evenObj D X)) M hM

end RMod.BrundanEllis.Stacking
