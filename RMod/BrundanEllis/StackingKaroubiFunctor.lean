import RMod.BrundanEllis.StackingKaroubiOrdinary
import RMod.BrundanEllis.StackingFunctorWhisker

/-! Every superfunctor extends to even idempotent corners by applying its
ordinary even functor to the projector and restricting its full Hom map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C D : Type} [SuperCategory C] [SuperCategory D]

def mapObject (F : SuperFunctor C D) (P : Karoubi (Even C)) : Karoubi (Even D) where
  X := F.forget.obj P.X
  p := F.forget.map P.p
  idem := by rw [← F.forget.map_comp, P.idem]

theorem map_projector (F : SuperFunctor C D) (P Q : Karoubi (Even C)) :
    F.map (ForgetEnrichment.to SuperVec P.X) (ForgetEnrichment.to SuperVec Q.X) ≫
      projector (mapObject F P) (mapObject F Q) =
    projector P Q ≫
      F.map (ForgetEnrichment.to SuperVec P.X) (ForgetEnrichment.to SuperVec Q.X) := by
  change F.map _ _ ≫ eHomWhiskerRight SuperVec (F.forget.map P.p) (F.forget.obj Q.X) ≫
      eHomWhiskerLeft SuperVec (F.forget.obj P.X) (F.forget.map Q.p) =
    (eHomWhiskerRight SuperVec P.p Q.X ≫ eHomWhiskerLeft SuperVec P.X Q.p) ≫ F.map _ _
  rw [superFunctor_pre_assoc, superFunctor_post, assoc]
  rfl

def mapHom (F : SuperFunctor C D) (P Q : Karoubi (Even C)) :
    homObject P Q ⟶ homObject (mapObject F P) (mapObject F Q) :=
  inclusion P Q ≫ F.map (ForgetEnrichment.to SuperVec P.X) (ForgetEnrichment.to SuperVec Q.X) ≫
    restriction (mapObject F P) (mapObject F Q)

@[reassoc] theorem mapHom_inclusion (F : SuperFunctor C D) (P Q : Karoubi (Even C)) :
    mapHom F P Q ≫ inclusion (mapObject F P) (mapObject F Q) =
    inclusion P Q ≫ F.map (ForgetEnrichment.to SuperVec P.X) (ForgetEnrichment.to SuperVec Q.X) := by
  simp only [mapHom, assoc, restriction_inclusion, map_projector]
  rw [← assoc, inclusion_projector]

def functor (F : SuperFunctor C D) : SuperFunctor (Karoubi (Even C)) (Karoubi (Even D)) where
  obj := mapObject F
  map := mapHom F
  map_id P := by
    apply (cancel_mono (inclusion (mapObject F P) (mapObject F P))).1
    change (identity P ≫ mapHom F P P) ≫ inclusion _ _ = identity (mapObject F P) ≫ inclusion _ _
    rw [assoc, mapHom_inclusion, ← assoc, identity_inclusion, identity_inclusion]
    rfl
  map_comp P Q R := by
    apply (cancel_mono (inclusion (mapObject F P) (mapObject F R))).1
    change (composition P Q R ≫ mapHom F P R) ≫ inclusion _ _ =
      ((mapHom F P Q ⊗ₘ mapHom F Q R) ≫ composition _ _ _) ≫ inclusion _ _
    simp only [assoc, mapHom_inclusion, composition_inclusion_assoc, composition_inclusion]
    rw [tensorHom_comp_tensorHom_assoc, mapHom_inclusion, mapHom_inclusion]
    rw [← tensorHom_comp_tensorHom_assoc]
    congr 1
    exact F.map_comp (ForgetEnrichment.to SuperVec P.X)
      (ForgetEnrichment.to SuperVec Q.X) (ForgetEnrichment.to SuperVec R.X)

end RMod.BrundanEllis.Stacking.KaroubiSuper
