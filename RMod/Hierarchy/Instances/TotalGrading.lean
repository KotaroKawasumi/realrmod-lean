import RMod.Hierarchy.Instances.TotalCategory
import RMod.Hierarchy.Instances.HomogeneousLine

/-!
# Homogeneous components of the total category

Every total morphism has a unique even-plus-odd decomposition. The
convolution composition adds degrees, as required by the legacy interface.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped BigOperators TensorProduct
namespace RMod.Legacy

variable (C : Supercategory)

/-- Projection to one homogeneous component, followed by its inclusion. -/
def homogeneousPart {X Y : C.data.Obj} (a : ZMod 2) (f : THom C.data X Y) :
    THom C.data X Y := fun b => if b = a then f b else 0

theorem homogeneousPart_mem {X Y : C.data.Obj} (a : ZMod 2) (f : THom C.data X Y) :
    homogeneousPart C a f ∈ grade C X Y a := by
  intro b hb
  simp [homogeneousPart, hb]

theorem homogeneousPart_add {X Y : C.data.Obj} (f : THom C.data X Y) :
    homogeneousPart C 0 f + homogeneousPart C 1 f = f := by
  funext a
  rcases Classification.parity_cases a with rfl | rfl <;>
    simp [homogeneousPart]

theorem grade_disjoint {X Y : C.data.Obj} (f : THom C.data X Y)
    (h₀ : f ∈ grade C X Y 0) (h₁ : f ∈ grade C X Y 1) : f = 0 := by
  funext a
  rcases Classification.parity_cases a with rfl | rfl
  · exact h₁ 0 zero_ne_one
  · exact h₀ 1 one_ne_zero

theorem evenPoint_mem_grade {X Y : C.data.Obj} (f : EHom C.data X Y) :
    evenPoint f ∈ grade C X Y 0 := by
  intro b hb
  simp [evenPoint, homogeneousPoint, hb]

theorem tComp_mem_grade {X Y Z : C.data.Obj} {a b : ZMod 2}
    (f : THom C.data X Y) (g : THom C.data Y Z)
    (hf : f ∈ grade C X Y a) (hg : g ∈ grade C Y Z b) :
    tComp C.data f g ∈ grade C X Z (a + b) := by
  intro c hc
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = a
  · subst i
    have hcb : c - a ≠ b := by
      intro h
      apply hc
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm b a)
    simp [hg (c - a) hcb]
  · simp [hf i hi]

end RMod.Legacy
