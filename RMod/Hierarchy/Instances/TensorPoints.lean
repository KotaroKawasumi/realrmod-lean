import RMod.Hierarchy.Abstract.MonoidalSupercategory
import RMod.Hierarchy.Instances.HomogeneousPoints

/-!
# Tensor products of even points

Evaluation at the basis vector commutes with tensoring even morphisms.
This lets total naturality restrict to the ordinary even category.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
open scoped TensorProduct BigOperators
namespace RMod.Legacy

theorem tTensor_even_left {C : SupercategoryData} (d : MonoidalSuperstructureData C)
    {X X' Y Y' : C.Obj} (f : EHom C X X') (g : THom C Y Y') (a : ZMod 2) :
    tTensor d (evenPoint f) g a = d.tensor.map (X, Y) (X', Y') a
      (ιTensorObj (C.Hom X X') (C.Hom Y Y') 0 a a (zero_add a)
        (evenPoint f 0 ⊗ₜ[ℝ] g a)) := by
  classical
  unfold tTensor
  rw [Finset.sum_eq_single 0]
  · rcases Classification.parity_cases a with rfl | rfl <;> rfl
  · intro b _ hb
    simp [evenPoint, homogeneousPoint, hb]
  · simp

theorem evenPoint_tensor {C : SupercategoryData} (d : MonoidalSuperstructureData C)
    {X X' Y Y' : C.Obj} (f : EHom C X X') (g : EHom C Y Y') :
    evenPoint (eTensor d f g) = tTensor d (evenPoint f) (evenPoint g) := by
  funext a
  rw [tTensor_even_left]
  by_cases ha : a = 0
  · subst a
    change ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g) ≫ d.tensor.map (X, Y) (X', Y')) 0
      ((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1) = _
    have hf := GradedObject.Monoidal.leftUnitor_inv_apply (tensorUnit : SuperVec) 0
    change (GradedObject.Monoidal.leftUnitor (tensorUnit : SuperVec)).inv 0 = _ at hf
    change d.tensor.map (X, Y) (X', Y') 0
      (GradedObject.Monoidal.tensorHom f g 0
        ((GradedObject.Monoidal.leftUnitor (tensorUnit : SuperVec)).inv 0
          ((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1))) = _
    rw [hf]
    have hfg := ι_tensorHom f g 0 0 0 (zero_add 0)
    have he := congrArg (fun q => q
      (((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1) ⊗ₜ[ℝ]
       ((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1))) hfg
    convert! congrArg (d.tensor.map (X, Y) (X', Y') 0) he
  · simp [evenPoint, homogeneousPoint, ha]

end RMod.Legacy
