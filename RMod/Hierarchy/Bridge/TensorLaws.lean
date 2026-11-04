import RMod.Hierarchy.Bridge.TensorData
import RMod.Hierarchy.Bridge.EvenCategory
import RMod.Hierarchy.Instances.TensorPoints
import RMod.Hierarchy.Instances.TensorInterchangePoints

/-!
# The old tensor becomes a superfunctor

Homogeneous generator calculations reduce the enriched composition law to
the old super-interchange law with the corrected chronological sign.
Even tensor products retain the old operations exactly.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem evenHomEquiv_tensor {X X' Y Y' : C.data.Obj}
    (f : EHom (ofOldSupercategoryData C) X X') (g : EHom (ofOldSupercategoryData C) Y Y') :
    evenHomEquiv C _ _ (eTensor (ofOldMonoidalStructureData C) f g) =
      evenHomEquiv C X X' f ⊗ₘ evenHomEquiv C Y Y' g := by
  apply WideSubcategory.hom_ext
  change (evenPoint (eTensor (ofOldMonoidalStructureData C) f g) 0).val = _
  rw [evenPoint_tensor, tTensor_even_left]
  change (oldTensorMap C X X' Y Y' 0
    (GradedObject.Monoidal.ιTensorObj (oldEnrichedHom C X X') (oldEnrichedHom C Y Y') 0 0 0 (zero_add 0)
      (evenPoint f 0 ⊗ₜ[ℝ] evenPoint g 0))).val = _
  rw [oldTensorMap_tmul, chronologicalTensor_even_left C.data C.laws]
  rfl

theorem ofOldTensor_map_id (X : C.data.Obj × C.data.Obj) :
    (superTensorProductData (ofOldSupercategoryData C) (ofOldSupercategoryData C)).id X ≫
      (ofOldTensorData C).map X X = (ofOldSupercategoryData C).id ((ofOldTensorData C).obj X) := by
  apply (evenHomEquiv C _ _).injective
  change evenHomEquiv C _ _ (eTensor (ofOldMonoidalStructureData C)
    ((ofOldSupercategoryData C).id X.1) ((ofOldSupercategoryData C).id X.2)) = _
  rw [evenHomEquiv_tensor, evenHomEquiv_id, evenHomEquiv_id, evenHomEquiv_id,
    MonoidalCategory.id_tensorHom_id]
  rfl

theorem ofOldTensor_map_comp (X Y Z : C.data.Obj × C.data.Obj) :
    (superTensorProductData (ofOldSupercategoryData C) (ofOldSupercategoryData C)).comp X Y Z ≫
      (ofOldTensorData C).map X Z =
    ((ofOldTensorData C).map X Y ⊗ₘ (ofOldTensorData C).map Y Z) ≫
      (ofOldSupercategoryData C).comp ((ofOldTensorData C).obj X)
        ((ofOldTensorData C).obj Y) ((ofOldTensorData C).obj Z) := by
  apply gradedFour_ext (oldEnrichedHom C X.1 Y.1) (oldEnrichedHom C X.2 Y.2)
    (oldEnrichedHom C Y.1 Z.1) (oldEnrichedHom C Y.2 Z.2)
  intro i j k l a ha f g q r
  change oldTensorMap C X.1 Z.1 X.2 Z.2 a
    ((oldEnrichedComp C X.1 Y.1 Z.1 ⊗ₘ oldEnrichedComp C X.2 Y.2 Z.2) a
      (tensorμ (oldEnrichedHom C X.1 Y.1) (oldEnrichedHom C X.2 Y.2)
        (oldEnrichedHom C Y.1 Z.1) (oldEnrichedHom C Y.2 Z.2) a
        (gradedTmul _ _ (i + j) (k + l) a _
          (gradedTmul _ _ i j (i + j) rfl f g)
          (gradedTmul _ _ k l (k + l) rfl q r)))) =
    oldEnrichedComp C (C.data.tensorObj X.1 X.2) (C.data.tensorObj Y.1 Y.2)
      (C.data.tensorObj Z.1 Z.2) a
      ((oldTensorMap C X.1 Y.1 X.2 Y.2 ⊗ₘ oldTensorMap C Y.1 Z.1 Y.2 Z.2) a
        (gradedTmul _ _ (i + j) (k + l) a _
          (gradedTmul _ _ i j (i + j) rfl f g)
          (gradedTmul _ _ k l (k + l) rfl q r)))
  erw [tensorμ_gradedTmul _ _ _ _ i j k l a ha f g q r, map_smul, map_smul,
    tensorHom_gradedTmul, tensorHom_gradedTmul]
  apply Subtype.ext
  change C.data.smul ((-1 : ℝ) ^ (j * k).val)
    (oldTensorMap C X.1 Z.1 X.2 Z.2 a
      (gradedTmul _ _ (i + k) (j + l) a _
        (oldEnrichedComp C X.1 Y.1 Z.1 (i + k) (gradedTmul _ _ i k (i + k) rfl f q))
        (oldEnrichedComp C X.2 Y.2 Z.2 (j + l) (gradedTmul _ _ j l (j + l) rfl g r)))).val = _
  unfold gradedTmul
  rw [oldTensorMap_tmul, oldEnrichedComp_tmul, oldEnrichedComp_tmul,
    oldEnrichedComp_tmul, oldTensorMap_tmul, oldTensorMap_tmul]
  exact (chronologicalTensor_interchange C.data C.laws i j k l
    f.val g.val q.val r.val f.property r.property).symm

theorem ofOldTensorLaws : SuperfunctorLaws (ofOldTensorData C) where
  map_id := ofOldTensor_map_id C
  map_comp := ofOldTensor_map_comp C

end RMod.Legacy.Hierarchy
