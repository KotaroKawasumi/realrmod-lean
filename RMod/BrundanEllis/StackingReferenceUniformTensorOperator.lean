import RMod.BrundanEllis.StackingReferenceOperatorTransport
import RMod.BrundanEllis.StackingReferenceTensorOperator

/-! The tensor of arbitrary morphisms in constant-label components acts by
the existing finite-family tensor operator. All transports retain the
original row enumerations and extract the original raw coefficients. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Coefficient extraction in a uniform row presentation reads the original coefficient. -/
theorem uniformRowValue_apply (a : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a)
    (f : Hom realDData X Y) (i : Fin X.size) (j : Fin Y.size) :
    rowValue a (fun i => (X.atom i).shift) (fun j => (Y.atom j).shift)
      (homTransport (rowObject_of_labels a X hX).symm (rowObject_of_labels a Y hY).symm f) j i =
      coefficientCast (hX i) ((f i j).coeff ((hX i).trans (hY j).symm)) := by
  exact homTransport_coeff (rowObject_of_labels a X hX).symm
    (rowObject_of_labels a Y hY).symm f i j ((hX i).trans (hY j).symm)

/-- Tensor operators for the actual objects are the finite-family operators in their row presentations. -/
theorem uniformOperator_tensor_uniform (a b : ZMod 8) (X X' Y Y' : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hX' : ∀ i, (X'.atom i).label = a)
    (hY : ∀ j, (Y.atom j).label = b) (hY' : ∀ j, (Y'.atom j).label = b)
    (hXY : ∀ i, ((Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).atom i).label = a + b)
    (hXY' : ∀ j, ((Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X' Y').atom j).label = a + b)
    (f : Hom realDData X X') (g : Hom realDData Y Y') :
    uniformOperator (a + b) _ _ hXY hXY'
      (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) f g) =
      ((objectRowTransport (uniformTensor_eq a b X' Y' hX' hY') (a + b)).toLinearMap.comp
        (familyTensorOperator a b (fun i => (X.atom i).shift) (fun i => (X'.atom i).shift)
          (fun j => (Y.atom j).shift) (fun j => (Y'.atom j).shift)
          (fun i i' => coefficientCast (hX i) ((f i i').coeff ((hX i).trans (hX' i').symm)))
          (fun j j' => coefficientCast (hY j) ((g j j').coeff ((hY j).trans (hY' j').symm))))).comp
        (objectRowTransport (uniformTensor_eq a b X Y hX hY) (a + b)).symm.toLinearMap := by
  let f' := homTransport (rowObject_of_labels a X hX).symm (rowObject_of_labels a X' hX').symm f
  let g' := homTransport (rowObject_of_labels b Y hY).symm (rowObject_of_labels b Y' hY').symm g
  have he : homTransport (uniformTensor_eq a b X Y hX hY) (uniformTensor_eq a b X' Y' hX' hY')
      (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) f' g') =
      Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) f g := by
    rw [tensorHom_transport (rowObject_of_labels a X hX) (rowObject_of_labels a X' hX')
      (rowObject_of_labels b Y hY) (rowObject_of_labels b Y' hY')]
    simp only [f', g', homTransport_roundtrip]
  rw [← he, uniformOperator_homTransport (a + b)
    (uniformTensor_eq a b X Y hX hY) (uniformTensor_eq a b X' Y' hX' hY')
    (fun _ => rfl) (fun _ => rfl) hXY hXY', uniformOperator_tensor_hom]
  have hf' : (fun i i' => rowValue a _ _ f' i' i) =
      (fun i i' => coefficientCast (hX i) ((f i i').coeff ((hX i).trans (hX' i').symm))) := by
    funext i i'
    exact uniformRowValue_apply a X X' hX hX' f i i'
  have hg' : (fun j j' => rowValue b _ _ g' j' j) =
      (fun j j' => coefficientCast (hY j) ((g j j').coeff ((hY j).trans (hY' j').symm))) := by
    funext j j'
    exact uniformRowValue_apply b Y Y' hY hY' g j j'
  rw [hf', hg']

/-- Pointwise evaluation of a family tensor operator retains its actual output slot. -/
theorem familyTensorOperator_apply {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (v : Fin (rowTensorObject a b p q).size → Coeff (a + b))
    (z : Fin (rowTensorObject a b p' q').size) :
    familyTensorOperator a b p p' q q' F G v z =
      (∑ i : Fin n, ∑ j : Fin m,
        shiftedTensorOperator a b (p i) (q j) (q' (rowTensorIndex a b p' q' z).2.1)
          (F i (rowTensorIndex a b p' q' z).1) (G j (rowTensorIndex a b p' q' z).2.1)
          (rowTensorCoordinates a b p q (Coeff (a + b)) v i j))
        (rowTensorIndex a b p' q' z).2.2 := by
  have h := congrFun (familyTensorOperator_coordinate a b p p' q q' F G v
    (rowTensorIndex a b p' q' z).1 (rowTensorIndex a b p' q' z).2.1)
      (rowTensorIndex a b p' q' z).2.2
  rw [rowTensorCoordinates_at] at h
  exact h

/-- Read the two original object rows and their fusion row in a uniform tensor. -/
def uniformTensorCoordinates (a b c : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b) :
    (Fin (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).size → Coeff c) ≃ₗ[ℝ]
      (Fin X.size → Fin Y.size → FusionTable.Index a b → Coeff c) :=
  (objectRowTransport (uniformTensor_eq a b X Y hX hY) c).symm.trans
    (rowTensorCoordinates a b (fun i => (X.atom i).shift) (fun j => (Y.atom j).shift) (Coeff c))

/-- The tensor of actual maps has the finite-family block formula in these coordinates. -/
theorem uniformOperator_tensor_coordinate (a b : ZMod 8) (X X' Y Y' : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hX' : ∀ i, (X'.atom i).label = a)
    (hY : ∀ j, (Y.atom j).label = b) (hY' : ∀ j, (Y'.atom j).label = b)
    (hXY : ∀ i, ((Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).atom i).label = a + b)
    (hXY' : ∀ j, ((Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X' Y').atom j).label = a + b)
    (f : Hom realDData X X') (g : Hom realDData Y Y')
    (v : Fin (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).size → Coeff (a + b))
    (i' : Fin X'.size) (j' : Fin Y'.size) :
    uniformTensorCoordinates a b (a + b) X' Y' hX' hY'
      (uniformOperator (a + b) _ _ hXY hXY'
        (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) f g) v) i' j' =
      ∑ i : Fin X.size, ∑ j : Fin Y.size,
        shiftedTensorOperator a b (X.atom i).shift (Y.atom j).shift (Y'.atom j').shift
          (coefficientCast (hX i) ((f i i').coeff ((hX i).trans (hX' i').symm)))
          (coefficientCast (hY j) ((g j j').coeff ((hY j).trans (hY' j').symm)))
          (uniformTensorCoordinates a b (a + b) X Y hX hY v i j) := by
  rw [uniformOperator_tensor_uniform a b X X' Y Y' hX hX' hY hY' hXY hXY' f g]
  change rowTensorCoordinates a b (fun i => (X'.atom i).shift) (fun j => (Y'.atom j).shift) _
    ((objectRowTransport (uniformTensor_eq a b X' Y' hX' hY') (a + b)).symm
      (objectRowTransport (uniformTensor_eq a b X' Y' hX' hY') (a + b)
        (familyTensorOperator a b _ _ _ _ _ _
          ((objectRowTransport (uniformTensor_eq a b X Y hX hY) (a + b)).symm v)))) i' j' = _
  rw [LinearEquiv.symm_apply_apply, familyTensorOperator_coordinate]
  rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
