import RMod.BrundanEllis.StackingKaroubiHom
import RMod.BrundanEllis.StackingEvenNaturality

/-! Composition and identities on the homogeneous Hom corners. Closure is
proved in the ambient enriched category before restricting to the image. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C]

theorem projector_pre (P Q : Karoubi (Even C)) :
    projector P Q ≫ eHomWhiskerRight SuperVec P.p Q.X = projector P Q := by
  have h := eHomWhiskerRight_comp SuperVec P.p P.p Q.X
  rw [P.idem] at h
  unfold projector
  rw [assoc, eHom_whisker_exchange, ← assoc, ← h]

theorem projector_post (P Q : Karoubi (Even C)) :
    projector P Q ≫ eHomWhiskerLeft SuperVec P.X Q.p = projector P Q := by
  have h := eHomWhiskerLeft_comp SuperVec P.X Q.p Q.p
  rw [Q.idem] at h
  unfold projector
  rw [assoc, ← h]

theorem inclusion_pre (P Q : Karoubi (Even C)) :
    inclusion P Q ≫ eHomWhiskerRight SuperVec P.p Q.X = inclusion P Q := by
  calc
    _ = (inclusion P Q ≫ projector P Q) ≫ eHomWhiskerRight SuperVec P.p Q.X := by
      rw [inclusion_projector]
    _ = _ := by rw [assoc, projector_pre, inclusion_projector]

theorem inclusion_post (P Q : Karoubi (Even C)) :
    inclusion P Q ≫ eHomWhiskerLeft SuperVec P.X Q.p = inclusion P Q := by
  calc
    _ = (inclusion P Q ≫ projector P Q) ≫ eHomWhiskerLeft SuperVec P.X Q.p := by
      rw [inclusion_projector]
    _ = _ := by rw [assoc, projector_post, inclusion_projector]

/-- Ambient composition of corner vectors remains in the outer corner. -/
theorem composition_closed (P Q R : Karoubi (Even C)) :
    (inclusion P Q ⊗ₘ inclusion Q R) ≫ eComp SuperVec P.X Q.X R.X ≫
      projector P R = (inclusion P Q ⊗ₘ inclusion Q R) ≫ eComp SuperVec P.X Q.X R.X := by
  unfold projector
  rw [eComp_eHomWhiskerRight_assoc, eComp_eHomWhiskerLeft]
  simp only [← tensorHom_id, ← id_tensorHom, ← assoc, tensorHom_comp_tensorHom,
    inclusion_pre, inclusion_post, Category.comp_id]

def composition (P Q R : Karoubi (Even C)) :
    homObject P Q ⊗ homObject Q R ⟶ homObject P R :=
  (inclusion P Q ⊗ₘ inclusion Q R) ≫ eComp SuperVec P.X Q.X R.X ≫ restriction P R

@[reassoc] theorem composition_inclusion (P Q R : Karoubi (Even C)) :
    composition P Q R ≫ inclusion P R =
      (inclusion P Q ⊗ₘ inclusion Q R) ≫ eComp SuperVec P.X Q.X R.X := by
  simp only [composition, assoc, restriction_inclusion, composition_closed]

/-- The identity of a corner is its idempotent, viewed in its own Hom image. -/
def identity (P : Karoubi (Even C)) : 𝟙_ SuperVec ⟶ homObject P P :=
  eHomEquiv SuperVec P.p ≫ restriction P P

@[reassoc] theorem identity_inclusion (P : Karoubi (Even C)) :
    identity P ≫ inclusion P P = eHomEquiv SuperVec P.p := by
  simp only [identity, assoc, restriction_inclusion, projector]
  rw [← assoc, even_pre, P.idem, even_post, P.idem]

end RMod.BrundanEllis.Stacking.KaroubiSuper
