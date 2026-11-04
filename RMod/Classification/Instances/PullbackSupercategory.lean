import RMod.Classification.Instances.PullbackLinearCategory
import Superfusion.Category.Even

/-!
# The existing supercategory interface on pullback Hom spaces

The two grading submodules are defined coordinatewise in the reference
category. Their internal direct sum and composition laws follow from the
same coordinatewise laws, independently of duality in the new category.
-/

set_option autoImplicit false

namespace RMod.Classification.PullbackCategory

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

def grade (X Y : PullbackCategory C hC t) (a : ZMod 2) : Submodule ℝ (X ⟶ Y) where
  carrier := {f | ∀ g, C.IsHomogeneous a (f g)}
  zero_mem' _ := hC.grade_zero _ _ _
  add_mem' hf hh g := hC.grade_add _ _ (hf g) (hh g)
  smul_mem' r _ hf g := hC.grade_smul r _ (hf g)

theorem grade_isCompl (X Y : PullbackCategory C hC t) :
    IsCompl (grade C hC t X Y 0) (grade C hC t X Y 1) := by
  constructor
  · exact Submodule.disjoint_def.mpr (fun f hf hh =>
      funext fun g => hC.grade_disjoint (f g) (hf g) (hh g))
  · apply Submodule.codisjoint_iff_exists_add_eq.mpr
    intro f
    choose f₀ f₁ h₀ h₁ he using fun g => hC.grade_decomposition (f g)
    exact ⟨f₀, f₁, h₀, h₁, funext he⟩

theorem grade_isInternal (X Y : PullbackCategory C hC t) :
    DirectSum.IsInternal (grade C hC t X Y) := by
  have he : (Set.univ : Set (ZMod 2)) = {0, 1} := by
    ext a
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    exact parity_cases a
  exact (DirectSum.isInternal_submodule_iff_isCompl _ zero_ne_one he).mpr
    (grade_isCompl C hC t X Y)

instance supercategory : Superfusion.Category.Supercategory ℝ (PullbackCategory C hC t) where
  grade := grade C hC t
  isInternal_grade := grade_isInternal C hC t
  id_mem_even X g := hC.id_even (X g).val
  comp_mem f h hf hh g := hC.comp_grade (f g) (h g) (hf g) (hh g)

end RMod.Classification.PullbackCategory
