import RMod.BrundanEllis.Foundation
import Mathlib.CategoryTheory.Idempotents.Karoubi

/-! Hom objects between even idempotent corners. The source and target
projectors act on the full enriched Hom, preserving every homogeneous degree. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C]

/-- Precomposition with the source corner projector, followed by postcomposition
with the target corner projector. -/
def projector (P Q : Karoubi (Even C)) :
    (P.X ⟶[SuperVec] Q.X) ⟶
      (P.X ⟶[SuperVec] Q.X) :=
  eHomWhiskerRight SuperVec P.p Q.X ≫ eHomWhiskerLeft SuperVec P.X Q.p

theorem projector_idem (P Q : Karoubi (Even C)) :
    projector P Q ≫ projector P Q = projector P Q := by
  have hr := eHomWhiskerRight_comp SuperVec P.p P.p Q.X
  have hl := eHomWhiskerLeft_comp SuperVec P.X Q.p Q.p
  rw [P.idem] at hr
  rw [Q.idem] at hl
  unfold projector
  calc
    _ = (eHomWhiskerRight SuperVec P.p Q.X ≫ eHomWhiskerRight SuperVec P.p Q.X) ≫
        (eHomWhiskerLeft SuperVec P.X Q.p ≫ eHomWhiskerLeft SuperVec P.X Q.p) := by
      rw [assoc, ← assoc (eHomWhiskerLeft SuperVec P.X Q.p), eHom_whisker_exchange]
      simp only [assoc]
    _ = _ := by rw [← hr, ← hl]


/-- The homogeneous vectors in the image of the two commuting projectors. -/
def homSubmodule (P Q : Karoubi (Even C)) (a : ZMod 2) :
    Submodule ℝ ((P.X ⟶[SuperVec] Q.X) a) :=
  LinearMap.range (projector P Q a).hom

def homObject (P Q : Karoubi (Even C)) : SuperVec :=
  fun a => ModuleCat.of ℝ (homSubmodule P Q a)

def inclusion (P Q : Karoubi (Even C)) : homObject P Q ⟶
    (P.X ⟶[SuperVec] Q.X) :=
  fun a => ModuleCat.ofHom (homSubmodule P Q a).subtype

/-- Projecting an arbitrary Hom vector already lands in its corner. -/
def restriction (P Q : Karoubi (Even C)) :
    (P.X ⟶[SuperVec] Q.X) ⟶
      homObject P Q := fun a => ModuleCat.ofHom (projector P Q a).hom.rangeRestrict

theorem restriction_inclusion (P Q : Karoubi (Even C)) :
    restriction P Q ≫ inclusion P Q = projector P Q := rfl

theorem inclusion_restriction (P Q : Karoubi (Even C)) :
    inclusion P Q ≫ restriction P Q = 𝟙 (homObject P Q) := by
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rcases x.property with ⟨y, hy⟩
  change (projector P Q a) x.val = x.val
  rw [← hy]
  exact congrArg (fun f => f a y) (projector_idem P Q)

theorem inclusion_projector (P Q : Karoubi (Even C)) :
    inclusion P Q ≫ projector P Q = inclusion P Q := by
  rw [← restriction_inclusion, ← assoc, inclusion_restriction, Category.id_comp]

end RMod.BrundanEllis.Stacking.KaroubiSuper
