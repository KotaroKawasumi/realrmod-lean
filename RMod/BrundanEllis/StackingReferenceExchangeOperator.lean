import RMod.BrundanEllis.StackingReferenceUniformOperator

/-! The uniform operator of the actual reference exchange is the original
normalized right-module exchange, with the actual tensor enumeration. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Matrix reconstruction and coefficient extraction are inverse. -/
theorem rowValue_rowHom {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (M : Matrix (Fin m) (Fin n) (Coeff a)) : rowValue a p q (rowHom a p q M) = M := by
  funext j i
  exact rowHom_coeff a p q M i j

/-- The raw tensor exchange acts by the specified normalized module operator. -/
theorem uniformOperator_tensorExchange {n m : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    uniformOperator (a + b) (rowTensorObject a b p q) (rowTensorObject b a q p)
      (fun _ => rfl) (fun _ => add_comm b a) (tensorExchange a b p q) =
      (rowTensorEquiv a b p q).toLinearMap := by
  unfold uniformOperator tensorExchange
  rw [homTransport_trans]
  change rowOperator (a + b)
    (rowValue (a + b) _ _
      (rowHom (a + b) _ _ (rowMatrixOf (a + b) (rowTensorEquiv a b p q).toLinearMap))) = _
  rw [rowValue_rowHom, rowOperator_matrixOf _ _ (rowTensorEquiv_right a b p q)]

/-- Object transport leaves the uniform row action unchanged when sizes agree definitionally. -/
theorem uniformOperator_rowPresentation (a : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a)
    (f : Hom realDData (rowObject a (fun i => (X.atom i).shift))
      (rowObject a (fun j => (Y.atom j).shift))) :
    uniformOperator a X Y hX hY
      (homTransport (rowObject_of_labels a X hX) (rowObject_of_labels a Y hY) f) =
      rowOperator a (rowValue a _ _ f) := by
  unfold uniformOperator
  rw [homTransport_trans]
  rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
