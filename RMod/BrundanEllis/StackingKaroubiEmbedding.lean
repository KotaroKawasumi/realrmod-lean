import RMod.BrundanEllis.StackingKaroubiOrdinary

/-! The original supercategory embeds into the completion at identity
projectors. Its Hom maps have explicit inverses in every degree. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable (C : Type) [SuperCategory C]

def original (X : C) : Karoubi (Even C) := (evenObj C X : Karoubi (Even C))

@[simp] theorem original_projector (X Y : C) :
    projector (original C X) (original C Y) = 𝟙 (SHom C X Y) := by
  simp only [projector, original, Karoubi.coe_p, eHomWhiskerRight_id,
    eHomWhiskerLeft_id, Category.id_comp]
  rfl

/-- Inclusion into trivial corners, with full graded Hom maps. -/
def embedding : SuperFunctor C (Karoubi (Even C)) where
  obj := original C
  map X Y := restriction (original C X) (original C Y)
  map_id X := by
    apply (cancel_mono (inclusion (original C X) (original C X))).1
    change (eId SuperVec X ≫ restriction (original C X) (original C X)) ≫
        inclusion (original C X) (original C X) =
      identity (original C X) ≫ inclusion (original C X) (original C X)
    rw [assoc, restriction_inclusion, original_projector, Category.comp_id, identity_inclusion]
    exact (eHomEquiv_id SuperVec (evenObj C X)).symm
  map_comp X Y Z := by
    apply (cancel_mono (inclusion (original C X) (original C Z))).1
    change (eComp SuperVec X Y Z ≫ restriction (original C X) (original C Z)) ≫
        inclusion (original C X) (original C Z) =
      ((restriction (original C X) (original C Y) ⊗ₘ restriction (original C Y) (original C Z)) ≫
        composition (original C X) (original C Y) (original C Z)) ≫
          inclusion (original C X) (original C Z)
    simp only [assoc, restriction_inclusion, original_projector, Category.comp_id,
      composition_inclusion, tensorHom_comp_tensorHom_assoc, id_tensorHom_id, Category.id_comp]
    change eComp SuperVec X Y Z =
      (𝟙 (SHom C X Y) ⊗ₘ 𝟙 (SHom C Y Z)) ≫ eComp SuperVec X Y Z
    rw [id_tensorHom_id, Category.id_comp]

theorem embedding_bijective (X Y : C) (a : ZMod 2) :
    Function.Bijective ((embedding C).map X Y a) := by
  have hi := congrArg (fun k => k a) (inclusion_restriction (original C X) (original C Y))
  have hr := congrArg (fun k => k a)
    ((restriction_inclusion (original C X) (original C Y)).trans (original_projector C X Y))
  constructor
  · intro f g h
    have h' := congrArg (fun x => inclusion (original C X) (original C Y) a x) h
    have hf := congrArg (fun k => k f) hr
    have hg := congrArg (fun k => k g) hr
    exact hf.symm.trans (h'.trans hg)
  · intro f
    refine ⟨inclusion (original C X) (original C Y) a f, ?_⟩
    exact congrArg (fun k => k f) hi

end RMod.BrundanEllis.Stacking.KaroubiSuper
