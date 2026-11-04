import RMod.BrundanEllis.StackingKaroubiMonoidal
import Mathlib.CategoryTheory.Monoidal.Functor

/-! The ordinary inclusion into the idempotent completion is strong
monoidal for the restricted tensor operations. Its comparisons are the
identity maps on the original objects, restricted to their trivial corners. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiTensor
variable (C : Type) [Category C] [MonoidalCategory C]

def inclusionMonoidal : (toKaroubi C).CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y := restrictIso (Iso.refl (X ⊗ Y)) (by simp [objectTensor, toKaroubi])
  μIso_hom_natural_left := by
    intros
    apply Karoubi.hom_ext
    simp [monoidalStruct, mapTensor, objectTensor, toKaroubi]
  μIso_hom_natural_right := by
    intros
    apply Karoubi.hom_ext
    simp [monoidalStruct, mapTensor, objectTensor, toKaroubi]
  associativity := by
    intros
    apply Karoubi.hom_ext
    simp [monoidalStruct, mapTensor, objectTensor, toKaroubi, associator]
  left_unitality := by
    intros
    apply Karoubi.hom_ext
    simp [monoidalStruct, mapTensor, objectTensor, toKaroubi, leftUnitor]
  right_unitality := by
    intros
    apply Karoubi.hom_ext
    simp [monoidalStruct, mapTensor, objectTensor, toKaroubi, rightUnitor]

end RMod.BrundanEllis.Stacking.KaroubiTensor
