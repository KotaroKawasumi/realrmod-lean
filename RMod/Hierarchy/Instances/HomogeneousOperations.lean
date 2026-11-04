import RMod.Hierarchy.Instances.TotalTensor
import RMod.Hierarchy.Instances.GradedTensorPoints

/-!
# Evaluation of operations on homogeneous morphisms

The finite convolution has one nonzero summand on homogeneous inputs.
These formulas connect total morphisms with generators of graded tensors.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
namespace RMod.Legacy

variable (C : Supercategory)

theorem homogeneous_ext {X Y : C.data.Obj} {a : ZMod 2}
    {f g : THom C.data X Y} (hf : f ∈ grade C X Y a) (hg : g ∈ grade C X Y a)
    (h : f a = g a) : f = g := by
  funext b
  by_cases hb : b = a
  · subst b
    exact h
  · exact (hf b hb).trans (hg b hb).symm

theorem tComp_homogeneous_at {X Y Z : C.data.Obj} (a b c : ZMod 2) (hab : a + b = c)
    (f : THom C.data X Y) (g : THom C.data Y Z)
    (hf : f ∈ grade C X Y a) :
    tComp C.data f g c = C.data.comp X Y Z c
      (gradedTmul (C.data.Hom X Y) (C.data.Hom Y Z) a b c hab (f a) (g b)) := by
  subst c
  unfold tComp
  rw [Finset.sum_eq_single a]
  · rcases Classification.parity_cases a with rfl | rfl <;>
      rcases Classification.parity_cases b with rfl | rfl <;> rfl
  · intro i _ hi
    simp [hf i hi]
  · simp

theorem tTensor_homogeneous_at (d : MonoidalSuperstructureData C.data)
    {X X' Y Y' : C.data.Obj} (a b c : ZMod 2) (hab : a + b = c)
    (f : THom C.data X X') (g : THom C.data Y Y')
    (hf : f ∈ grade C X X' a) :
    tTensor d f g c = d.tensor.map (X, Y) (X', Y') c
      (gradedTmul (C.data.Hom X X') (C.data.Hom Y Y') a b c hab (f a) (g b)) := by
  subst c
  unfold tTensor
  rw [Finset.sum_eq_single a]
  · rcases Classification.parity_cases a with rfl | rfl <;>
      rcases Classification.parity_cases b with rfl | rfl <;> rfl
  · intro i _ hi
    simp [hf i hi]
  · simp

end RMod.Legacy
