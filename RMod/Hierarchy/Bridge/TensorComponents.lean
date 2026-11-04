import RMod.Hierarchy.Bridge.TensorData
import RMod.Hierarchy.Bridge.TotalHom
import RMod.Classification.Proofs.TensorCalculus

/-!
# Component formulas for the transported tensor

Only the odd-odd summand changes sign. These formulas extend homogeneous
coherence identities to arbitrary total morphisms by bilinearity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem ofOld_tTensor_zero {X X' Y Y' : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X X') (g : THom (ofOldSupercategoryData C) Y Y') :
    (tTensor (ofOldMonoidalStructureData C) f g 0).val =
      C.data.add (C.data.tensorHom (f 0).val (g 0).val)
        (C.data.smul (-1) (C.data.tensorHom (f 1).val (g 1).val)) := by
  unfold tTensor
  erw [Fin.sum_univ_two]
  change (oldTensorMap C X X' Y Y' 0
    (GradedObject.Monoidal.ιTensorObj (oldEnrichedHom C X X') (oldEnrichedHom C Y Y')
      0 0 0 rfl (f 0 ⊗ₜ[ℝ] g 0) +
    GradedObject.Monoidal.ιTensorObj (oldEnrichedHom C X X') (oldEnrichedHom C Y Y')
      1 1 0 rfl (f 1 ⊗ₜ[ℝ] g 1))).val = _
  rw [map_add]
  change C.data.add _ _ = _
  rw [oldTensorMap_tmul, oldTensorMap_tmul, chronologicalTensor_even_left C.data C.laws]
  simp only [chronologicalTensor, mul_one, ZMod.val_one, pow_one]

theorem ofOld_tTensor_one {X X' Y Y' : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X X') (g : THom (ofOldSupercategoryData C) Y Y') :
    (tTensor (ofOldMonoidalStructureData C) f g 1).val =
      C.data.add (C.data.tensorHom (f 0).val (g 1).val)
        (C.data.tensorHom (f 1).val (g 0).val) := by
  unfold tTensor
  erw [Fin.sum_univ_two]
  change (oldTensorMap C X X' Y Y' 1
    (GradedObject.Monoidal.ιTensorObj (oldEnrichedHom C X X') (oldEnrichedHom C Y Y')
      0 1 1 rfl (f 0 ⊗ₜ[ℝ] g 1) +
    GradedObject.Monoidal.ιTensorObj (oldEnrichedHom C X X') (oldEnrichedHom C Y Y')
      1 0 1 rfl (f 1 ⊗ₜ[ℝ] g 0))).val = _
  rw [map_add]
  change C.data.add _ _ = _
  rw [oldTensorMap_tmul, oldTensorMap_tmul, chronologicalTensor_even_left C.data C.laws,
    chronologicalTensor_even_right C.data C.laws]

theorem totalHomEquiv_even (X Y : C.data.Obj) (f : EHom (ofOldSupercategoryData C) X Y) :
    totalHomEquiv C X Y (evenPoint f) = (evenPoint f 0).val := by
  rw [totalHomEquiv_apply]
  have h : (evenPoint f 1).val = C.data.zero := by
    simp [evenPoint, homogeneousPoint]
    rfl
  rw [h, C.laws.add_zero]

theorem totalHomEquiv_tTensor {X X' Y Y' : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X X') (g : THom (ofOldSupercategoryData C) Y Y') :
    totalHomEquiv C _ _ (tTensor (ofOldMonoidalStructureData C) f g) =
      C.data.add
        (C.data.add (C.data.tensorHom (f 0).val (g 0).val)
          (C.data.smul (-1) (C.data.tensorHom (f 1).val (g 1).val)))
        (C.data.add (C.data.tensorHom (f 0).val (g 1).val)
          (C.data.tensorHom (f 1).val (g 0).val)) := by
  rw [totalHomEquiv_apply, ofOld_tTensor_zero, ofOld_tTensor_one]

theorem evenPoint_one_val {X Y : C.data.Obj} (f : EHom (ofOldSupercategoryData C) X Y) :
    (evenPoint f 1).val = C.data.zero := by
  simp [evenPoint, homogeneousPoint]
  rfl

theorem totalHomEquiv_tTensor_even_left {X X' Y Y' : C.data.Obj}
    (f : EHom (ofOldSupercategoryData C) X X') (g : THom (ofOldSupercategoryData C) Y Y') :
    totalHomEquiv C _ _ (tTensor (ofOldMonoidalStructureData C) (evenPoint f) g) =
      C.data.tensorHom (evenPoint f 0).val (totalHomEquiv C Y Y' g) := by
  rw [totalHomEquiv_tTensor, evenPoint_one_val]
  simp only [Classification.tensor_zero_left C.laws, C.laws.smul_zero, C.laws.add_zero,
    totalHomEquiv_apply, C.laws.tensor_add_right]

theorem totalHomEquiv_tTensor_even_right {X X' Y Y' : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X X') (g : EHom (ofOldSupercategoryData C) Y Y') :
    totalHomEquiv C _ _ (tTensor (ofOldMonoidalStructureData C) f (evenPoint g)) =
      C.data.tensorHom (totalHomEquiv C X X' f) (evenPoint g 0).val := by
  rw [totalHomEquiv_tTensor, evenPoint_one_val]
  simp only [Classification.tensor_zero_right C.laws, C.laws.smul_zero, C.laws.add_zero,
    C.laws.zero_add, totalHomEquiv_apply, C.laws.tensor_add_left]

end RMod.Legacy.Hierarchy
