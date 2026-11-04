import RMod.Hierarchy.Abstract.MonoidalSupercategory
import RMod.Hierarchy.Bridge.EnrichmentData
import RMod.Hierarchy.Bridge.TensorConvention
import RMod.Hierarchy.Instances.HomogeneousLine

/-!
# Enriched monoidal operations from the old tensor convention

On degrees i and j, the new tensor is (-1)^(ij) times the old tensor.
The associator and unitors are the specified old even maps, represented as
maps from the even real line. Thus no coherence operation is chosen afresh.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

def oldGradedTensor (X X' Y Y' : C.data.Obj) (i j a : ZMod 2) (h : i + j = a) :
    Classification.LinearCategory.grade C X X' i →ₗ[ℝ]
      Classification.LinearCategory.grade C Y Y' j →ₗ[ℝ]
        Classification.LinearCategory.grade C (C.data.tensorObj X Y) (C.data.tensorObj X' Y') a where
  toFun f :=
    { toFun g := ⟨chronologicalTensor C.data i j f.val g.val, by
        change C.data.smul _ (C.data.tensorHom f.val g.val) ∈ C.data.grade _ _ a
        rw [← h]
        exact C.laws.grade_smul _ _ (C.laws.tensor_grade _ _ f.property g.property)⟩
      map_add' g q := Subtype.ext (by
        change C.data.smul _ (C.data.tensorHom f.val (C.data.add g.val q.val)) = _
        rw [C.laws.tensor_add_right, C.laws.smul_add]
        rfl)
      map_smul' r g := Subtype.ext (by
        change C.data.smul _ (C.data.tensorHom f.val (C.data.smul r g.val)) =
          C.data.smul r (C.data.smul _ (C.data.tensorHom f.val g.val))
        rw [C.laws.tensor_smul_right, ← C.laws.mul_smul, ← C.laws.mul_smul, mul_comm]) }
  map_add' f g := LinearMap.ext fun q => Subtype.ext (by
    change C.data.smul _ (C.data.tensorHom (C.data.add f.val g.val) q.val) = _
    rw [C.laws.tensor_add_left, C.laws.smul_add]
    rfl)
  map_smul' r f := LinearMap.ext fun g => Subtype.ext (by
    change C.data.smul _ (C.data.tensorHom (C.data.smul r f.val) g.val) =
      C.data.smul r (C.data.smul _ (C.data.tensorHom f.val g.val))
    rw [C.laws.tensor_smul_left, ← C.laws.mul_smul, ← C.laws.mul_smul, mul_comm])

def oldTensorMap (X X' Y Y' : C.data.Obj) :
    oldEnrichedHom C X X' ⊗ oldEnrichedHom C Y Y' ⟶
      oldEnrichedHom C (C.data.tensorObj X Y) (C.data.tensorObj X' Y') := fun a =>
  GradedObject.Monoidal.tensorObjDesc fun i j h =>
    ModuleCat.ofHom (TensorProduct.lift (oldGradedTensor C X X' Y Y' i j a h))

def ofOldTensorData : SuperfunctorData
    (superTensorProductData (ofOldSupercategoryData C) (ofOldSupercategoryData C))
    (ofOldSupercategoryData C) where
  obj X := C.data.tensorObj X.1 X.2
  map X Y := oldTensorMap C X.1 Y.1 X.2 Y.2

def ofOldMonoidalStructureData : MonoidalSuperstructureData (ofOldSupercategoryData C) where
  tensor := ofOldTensorData C
  unit := C.data.tensorUnit
  associatorHom X Y Z := homogeneousMap _ 0
    ⟨C.data.associatorHom X Y Z, C.laws.associator_hom_even X Y Z⟩
  associatorInv X Y Z := homogeneousMap _ 0
    ⟨C.data.associatorInv X Y Z, C.laws.associator_inv_even X Y Z⟩
  leftHom X := homogeneousMap _ 0 ⟨C.data.leftUnitorHom X, C.laws.left_unitor_hom_even X⟩
  leftInv X := homogeneousMap _ 0 ⟨C.data.leftUnitorInv X, C.laws.left_unitor_inv_even X⟩
  rightHom X := homogeneousMap _ 0 ⟨C.data.rightUnitorHom X, C.laws.right_unitor_hom_even X⟩
  rightInv X := homogeneousMap _ 0 ⟨C.data.rightUnitorInv X, C.laws.right_unitor_inv_even X⟩

theorem oldTensorMap_tmul (X X' Y Y' : C.data.Obj) (i j a : ZMod 2) (h : i + j = a)
    (f : Classification.LinearCategory.grade C X X' i)
    (g : Classification.LinearCategory.grade C Y Y' j) :
    (oldTensorMap C X X' Y Y' a
      (GradedObject.Monoidal.ιTensorObj (oldEnrichedHom C X X') (oldEnrichedHom C Y Y')
        i j a h (f ⊗ₜ[ℝ] g))).val = chronologicalTensor C.data i j f.val g.val := by
  have he := GradedObject.Monoidal.ι_tensorObjDesc
    (X₁ := oldEnrichedHom C X X') (X₂ := oldEnrichedHom C Y Y')
    (fun i j h => ModuleCat.ofHom (TensorProduct.lift (oldGradedTensor C X X' Y Y' i j a h))) i j h
  exact congrArg (fun q => (q (f ⊗ₜ[ℝ] g)).val) he

end RMod.Legacy.Hierarchy
