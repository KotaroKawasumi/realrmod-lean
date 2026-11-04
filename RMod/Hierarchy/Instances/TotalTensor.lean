import RMod.Hierarchy.Abstract.MonoidalSupercategory
import RMod.Hierarchy.Instances.TotalGrading

/-!
# Bilinearity and grading of the total tensor operation

The tensor superfunctor induces a bilinear operation on total morphisms.
Its homogeneous components have the sum of the two input degrees.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace RMod.Legacy

variable {C : SupercategoryData} (d : MonoidalSuperstructureData C)

theorem tTensor_add_left {X X' Y Y' : C.Obj}
    (f f' : THom C X X') (g : THom C Y Y') :
    tTensor d (f + f') g = tTensor d f g + tTensor d f' g := by
  funext a
  simp [tTensor, TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]

theorem tTensor_add_right {X X' Y Y' : C.Obj}
    (f : THom C X X') (g g' : THom C Y Y') :
    tTensor d f (g + g') = tTensor d f g + tTensor d f g' := by
  funext a
  simp [tTensor, TensorProduct.tmul_add, map_add, Finset.sum_add_distrib]

theorem tTensor_smul_left {X X' Y Y' : C.Obj}
    (r : ℝ) (f : THom C X X') (g : THom C Y Y') :
    tTensor d (r • f) g = r • tTensor d f g := by
  funext a
  simp [tTensor, ← TensorProduct.smul_tmul', map_smul, Finset.smul_sum]

theorem tTensor_smul_right {X X' Y Y' : C.Obj}
    (r : ℝ) (f : THom C X X') (g : THom C Y Y') :
    tTensor d f (r • g) = r • tTensor d f g := by
  funext a
  simp [tTensor, TensorProduct.tmul_smul, map_smul, Finset.smul_sum]

theorem tTensor_zero_left {X X' Y Y' : C.Obj} (g : THom C Y Y') :
    tTensor d (0 : THom C X X') g = 0 := by
  funext a
  simp [tTensor]

theorem tTensor_zero_right {X X' Y Y' : C.Obj} (f : THom C X X') :
    tTensor d f (0 : THom C Y Y') = 0 := by
  funext a
  simp [tTensor]

theorem tTensor_mem_grade (S : Supercategory) (d : MonoidalSuperstructureData S.data)
    {X X' Y Y' : S.data.Obj} {a b : ZMod 2}
    (f : THom S.data X X') (g : THom S.data Y Y')
    (hf : f ∈ grade S X X' a) (hg : g ∈ grade S Y Y' b) :
    tTensor d f g ∈ grade S (d.tensor.obj (X, Y)) (d.tensor.obj (X', Y')) (a + b) := by
  intro c hc
  change d.tensor.map (X, Y) (X', Y') c _ = 0
  rw [← map_zero (d.tensor.map (X, Y) (X', Y') c).hom]
  congr 1
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
