import RMod.BrundanEllis.StackingFaithfulForget
import RMod.BrundanEllis.StackingHomConjugation

/-! A full graded Hom isomorphism and chosen even representatives determine
a genuine enriched inverse functor. Its laws follow by cancelling the
forward Hom isomorphism, so no assumption about odd naturality is added. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
  (R : D → C) (e : ∀ X : D, F.forget.obj (evenObj C (R X)) ≅ evenObj D X)

/-- Conjugate into the chosen representatives, then use the actual Hom inverse. -/
def inverseHom (X Y : D) : SHom D X Y ⟶ SHom C (R X) (R Y) :=
  (Iso.eHomCongr SuperVec (e X) (e Y)).inv ≫ (superHomIso F hF (R X) (R Y)).inv

@[reassoc] theorem inverseHom_map (X Y : D) :
    inverseHom F hF R e X Y ≫ F.map (R X) (R Y) =
      (Iso.eHomCongr SuperVec (e X) (e Y)).inv := by
  change (_ ≫ (superHomIso F hF (R X) (R Y)).inv) ≫
    (superHomIso F hF (R X) (R Y)).hom = _
  rw [assoc, Iso.inv_hom_id, Category.comp_id]

def enrichedInverse : SuperFunctor D C where
  obj := R
  map := inverseHom F hF R e
  map_id X := by
    apply (cancel_mono (superHomIso F hF (R X) (R X)).hom).1
    change (eId SuperVec X ≫ inverseHom F hF R e X X) ≫ F.map (R X) (R X) =
      eId SuperVec (R X) ≫ F.map (R X) (R X)
    rw [assoc, inverseHom_map, F.map_id]
    exact homCongr_identity (e X).symm
  map_comp X Y Z := by
    apply (cancel_mono (superHomIso F hF (R X) (R Z)).hom).1
    change (eComp SuperVec X Y Z ≫ inverseHom F hF R e X Z) ≫ F.map (R X) (R Z) =
      ((inverseHom F hF R e X Y ⊗ₘ inverseHom F hF R e Y Z) ≫
        eComp SuperVec (R X) (R Y) (R Z)) ≫ F.map (R X) (R Z)
    simp only [assoc, inverseHom_map, F.map_comp, tensorHom_comp_tensorHom_assoc]
    exact (homCongr_composition (e X).symm (e Y).symm (e Z).symm).symm

/-- The lifted inverse is fully faithful in every degree. -/
theorem enrichedInverse_bijective (X Y : D) (a : ZMod 2) :
    Function.Bijective ((enrichedInverse F hF R e).map X Y a) := by
  let u := (Iso.eHomCongr SuperVec (e X) (e Y)).symm ≪≫
    (superHomIso F hF (R X) (R Y)).symm
  have hl : Function.LeftInverse (u.inv a) (u.hom a) := by
    intro x
    exact congrArg (fun f => f a x) u.hom_inv_id
  have hr : Function.RightInverse (u.inv a) (u.hom a) := by
    intro x
    exact congrArg (fun f => f a x) u.inv_hom_id
  exact ⟨hl.injective, hr.surjective⟩

end RMod.BrundanEllis.Stacking
