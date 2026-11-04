import RMod.BrundanEllis.StackingReferenceExchangeOperator

/-! Tensoring actual reference morphisms induces the previously specified
finite-family operator. This identifies the tensor legs of the reference
hexagons without replacing the category's given tensor product. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- The stored tensor coefficients act by the finite-family tensor operator. -/
theorem uniformOperator_tensor_rows {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) :
    uniformOperator (a + b) (rowTensorObject a b p q) (rowTensorObject a b p' q')
      (fun _ => rfl) (fun _ => rfl)
      (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
        (rowHom a p p' (fun i' i => F i i')) (rowHom b q q' (fun j' j => G j j'))) =
      familyTensorOperator a b p p' q q' F G := by
  rw [← familyTensorOperator_actual]
  unfold uniformOperator
  change rowOperator (a + b)
    (rowValue (a + b) _ _ (rowHom (a + b) _ _
      (rowMatrixOf (a + b) (familyTensorOperator a b p p' q q' F G)))) = _
  rw [rowValue_rowHom, rowOperator_matrixOf _ _ (familyTensorOperator_right a b p p' q q' F G)]

/-- No homogeneity restriction is needed for the underlying tensor operator. -/
theorem uniformOperator_tensor_hom {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (f : Hom realDData (rowObject a p) (rowObject a p'))
    (g : Hom realDData (rowObject b q) (rowObject b q')) :
    uniformOperator (a + b) (rowTensorObject a b p q) (rowTensorObject a b p' q')
      (fun _ => rfl) (fun _ => rfl)
      (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) f g) =
      familyTensorOperator a b p p' q q'
        (fun i i' => rowValue a p p' f i' i) (fun j j' => rowValue b q q' g j' j) := by
  have h := uniformOperator_tensor_rows a b p p' q q'
    (fun i i' => rowValue a p p' f i' i) (fun j j' => rowValue b q q' g j' j)
  simpa only [rowHom_rowValue] using h

end RMod.BrundanEllis.Stacking.ReferenceCommutor
