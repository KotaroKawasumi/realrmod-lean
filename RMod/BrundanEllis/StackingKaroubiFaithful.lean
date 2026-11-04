import RMod.BrundanEllis.StackingKaroubiFunctor
import RMod.BrundanEllis.StackingFaithfulForget

/-! Full graded faithfulness survives completion. The inverse on a Hom
corner is the ambient Hom inverse restricted to the source corner; the
projector comparison proves both inverse laws. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))

def mapHomIso (P Q : Karoubi (Even C)) :
    homObject P Q ≅ homObject (mapObject F P) (mapObject F Q) where
  hom := mapHom F P Q
  inv := inclusion (mapObject F P) (mapObject F Q) ≫
    (superHomIso F hF (ForgetEnrichment.to SuperVec P.X) (ForgetEnrichment.to SuperVec Q.X)).inv ≫
      restriction P Q
  hom_inv_id := by
    rw [mapHom_inclusion_assoc]
    change inclusion P Q ≫
      (superHomIso F hF (ForgetEnrichment.to SuperVec P.X) (ForgetEnrichment.to SuperVec Q.X)).hom ≫
      (superHomIso F hF (ForgetEnrichment.to SuperVec P.X) (ForgetEnrichment.to SuperVec Q.X)).inv ≫
        restriction P Q = _
    rw [Iso.hom_inv_id_assoc, inclusion_restriction]
  inv_hom_id := by
    let e : (P.X ⟶[SuperVec] Q.X) ≅ ((mapObject F P).X ⟶[SuperVec] (mapObject F Q).X) :=
      superHomIso F hF (ForgetEnrichment.to SuperVec P.X) (ForgetEnrichment.to SuperVec Q.X)
    change (inclusion (mapObject F P) (mapObject F Q) ≫ e.inv ≫ restriction P Q) ≫
      inclusion P Q ≫ e.hom ≫ restriction (mapObject F P) (mapObject F Q) = _
    simp only [assoc]
    rw [← assoc (restriction P Q) (inclusion P Q), restriction_inclusion]
    have hp : e.hom ≫ projector (mapObject F P) (mapObject F Q) = projector P Q ≫ e.hom :=
      map_projector F P Q
    rw [← assoc (projector P Q) e.hom, ← hp, assoc, Iso.inv_hom_id_assoc,
      ← assoc, inclusion_projector, inclusion_restriction]

include hF in

theorem functor_bijective (P Q : Karoubi (Even C)) (a : ZMod 2) :
    Function.Bijective ((functor F).map P Q a) := by
  let e := mapHomIso F hF P Q
  have hl : Function.LeftInverse (e.inv a) ((functor F).map P Q a) := by
    intro x
    exact congrArg (fun k => k a x) e.hom_inv_id
  have hr : Function.RightInverse (e.inv a) ((functor F).map P Q a) := by
    intro x
    exact congrArg (fun k => k a x) e.inv_hom_id
  exact ⟨hl.injective, hr.surjective⟩

end RMod.BrundanEllis.Stacking.KaroubiSuper
