import RMod.Hierarchy.Bridge.TotalCategory

/-!
# Preservation of homogeneous morphisms

Reassembling the two components identifies support in a single parity with
membership in the old grading submodule. The reverse implication uses the
old direct-sum condition, not a choice of homogeneous representatives.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy

theorem mem_grade_zero (C : Supercategory) (X Y : TotalCategory C) (f : THom C.data X Y) :
    f ∈ grade C X Y 0 ↔ f 1 = 0 := by
  constructor
  · intro h
    exact h 1 one_ne_zero
  · intro h b hb
    rcases Classification.parity_cases b with rfl | rfl
    · exact (hb rfl).elim
    · exact h

theorem mem_grade_one (C : Supercategory) (X Y : TotalCategory C) (f : THom C.data X Y) :
    f ∈ grade C X Y 1 ↔ f 0 = 0 := by
  constructor
  · intro h
    exact h 0 zero_ne_one
  · intro h b hb
    rcases Classification.parity_cases b with rfl | rfl
    · exact h
    · exact (hb rfl).elim

namespace Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem totalHomEquiv_grade (X Y : Classification.LinearCategory C)
    (f : THom (ofOldSupercategoryData C) X Y) (a : ZMod 2) :
    f ∈ grade (ofOldSupercategory C) X Y a ↔
      totalHomEquiv C X Y f ∈ Classification.LinearCategory.grade C X Y a := by
  rcases Classification.parity_cases a with rfl | rfl
  · erw [mem_grade_zero, totalHomEquiv_apply]
    change f 1 = 0 ↔ (f 0).val + (f 1).val ∈ Classification.LinearCategory.grade C X Y 0
    erw [Submodule.add_mem_iff_right _ (f 0).property]
    constructor
    · intro h
      rw [h]
      exact Submodule.zero_mem _
    · intro h
      apply Subtype.ext
      exact C.laws.grade_disjoint _ h (f 1).property
  · erw [mem_grade_one, totalHomEquiv_apply]
    change f 0 = 0 ↔ (f 0).val + (f 1).val ∈ Classification.LinearCategory.grade C X Y 1
    erw [Submodule.add_mem_iff_left _ (f 1).property]
    constructor
    · intro h
      rw [h]
      exact Submodule.zero_mem _
    · intro h
      apply Subtype.ext
      exact C.laws.grade_disjoint _ (f 0).property h

end Hierarchy
end RMod.Legacy
