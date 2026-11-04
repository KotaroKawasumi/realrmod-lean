import RMod.BrundanEllis.StackingReferenceLabelOperator
import RMod.BrundanEllis.StackingReferenceExchangeOperator

/-! Faithful row operators respect identity maps, changes of objects, and
changes of the common division-algebra label. These are the transport rules
needed to identify the threefold kernel diagrams with categorical diagrams. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Transporting an object transports its original row enumeration. -/
def objectRowTransport {X Y : Obj} (h : X = Y) (a : ZMod 8) :
    (Fin X.size → Coeff a) ≃ₗ[ℝ] (Fin Y.size → Coeff a) := by
  cases h
  exact LinearEquiv.refl ℝ _

/-- The transport preserves each numerical row position. -/
theorem objectRowTransport_apply {X Y : Obj} (h : X = Y) (a : ZMod 8)
    (v : Fin X.size → Coeff a) (j : Fin Y.size) :
    objectRowTransport h a v j = v (Fin.cast (congrArg Obj.size h).symm j) := by
  cases h
  rfl

/-- The inverse object transport reads the same position in the other enumeration. -/
theorem objectRowTransport_symm_apply {X Y : Obj} (h : X = Y) (a : ZMod 8)
    (v : Fin Y.size → Coeff a) (i : Fin X.size) :
    (objectRowTransport h a).symm v i = v (Fin.cast (congrArg Obj.size h) i) := by
  cases h
  rfl

/-- Object transport preserves the identity morphism. -/
theorem homTransport_id {X Y : Obj} (h : X = Y) :
    homTransport h h (Hom.id realDData X) = Hom.id realDData Y := by
  cases h
  rfl

/-- Identity morphisms act as identity row operators. -/
theorem uniformOperator_id (a : ZMod 8) (X : Obj) (hX : ∀ i, (X.atom i).label = a) :
    uniformOperator a X X hX hX (Hom.id realDData X) = LinearMap.id := by
  unfold uniformOperator
  rw [homTransport_id, ← rowHom_identity, rowValue_rowHom, rowOperator_identity]

/-- Changing the object presentation only conjugates the row operator by its enumeration transport. -/
theorem uniformOperator_homTransport (a : ZMod 8) {X Y X' Y' : Obj}
    (hx : X = X') (hy : Y = Y')
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a)
    (hX' : ∀ i, (X'.atom i).label = a) (hY' : ∀ j, (Y'.atom j).label = a)
    (f : Hom realDData X Y) :
    uniformOperator a X' Y' hX' hY' (homTransport hx hy f) =
      ((objectRowTransport hy a).toLinearMap.comp (uniformOperator a X Y hX hY f)).comp
        (objectRowTransport hx a).symm.toLinearMap := by
  cases hx
  cases hy
  rfl

/-- Changing the common algebra label conjugates by coefficient transport. -/
theorem uniformOperator_labelCast {a b : ZMod 8} (h : a = b) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a)
    (f : Hom realDData X Y) :
    uniformOperator b X Y (fun i => (hX i).trans h) (fun j => (hY j).trans h) f =
      ((rowCoefficientCast h).toLinearMap.comp (uniformOperator a X Y hX hY f)).comp
        (rowCoefficientCast h).symm.toLinearMap := by
  cases h
  rfl

/-- The separately labelled operator has the same object transport rule. -/
theorem labelOperator_homTransport (a b : ZMod 8) {X Y X' Y' : Obj}
    (hx : X = X') (hy : Y = Y') (hab : a = b)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (hX' : ∀ i, (X'.atom i).label = a) (hY' : ∀ j, (Y'.atom j).label = b)
    (f : Hom realDData X Y) :
    labelOperator a b X' Y' hX' hY' hab (homTransport hx hy f) =
      ((objectRowTransport hy b).toLinearMap.comp (labelOperator a b X Y hX hY hab f)).comp
        (objectRowTransport hx a).symm.toLinearMap := by
  cases hx
  cases hy
  rfl

/-- Reparenthesizing the source label is precomposition by coefficient transport. -/
theorem labelOperator_source_cast {a b c : ZMod 8} (h : a = b) (k : b = c) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = c)
    (f : Hom realDData X Y) :
    labelOperator a c X Y hX hY (h.trans k) f =
      (labelOperator b c X Y (fun i => (hX i).trans h) hY k f).comp
        (rowCoefficientCast h).toLinearMap := by
  cases h
  rfl

/-- Reparenthesizing the target label is postcomposition by coefficient transport. -/
theorem labelOperator_target_cast {a b c : ZMod 8} (h : a = b) (k : b = c) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (f : Hom realDData X Y) :
    labelOperator a c X Y hX (fun j => (hY j).trans k) (h.trans k) f =
      (rowCoefficientCast k).toLinearMap.comp (labelOperator a b X Y hX hY h f) := by
  cases k
  rfl

/-- The actual uniform exchange is conjugation of the normalized row exchange. -/
theorem uniformOperator_uniformExchange (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (hXY : ∀ i, ((Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).atom i).label = a + b)
    (hYX : ∀ j, ((Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) Y X).atom j).label = a + b) :
    uniformOperator (a + b) _ _ hXY hYX (uniformExchange a b X Y hX hY) =
      ((objectRowTransport (uniformTensor_eq b a Y X hY hX) (a + b)).toLinearMap.comp
        (rowTensorEquiv a b (fun i => (X.atom i).shift) (fun j => (Y.atom j).shift)).toLinearMap).comp
          (objectRowTransport (uniformTensor_eq a b X Y hX hY) (a + b)).symm.toLinearMap := by
  unfold uniformExchange
  rw [uniformOperator_homTransport (a + b)
    (uniformTensor_eq a b X Y hX hY) (uniformTensor_eq b a Y X hY hX)
    (fun _ => rfl) (fun _ => add_comm b a) hXY hYX,
    uniformOperator_tensorExchange]

/-- Pointwise form avoids expanding the composed linear maps. -/
theorem uniformOperator_uniformExchange_apply (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (hXY : ∀ i, ((Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).atom i).label = a + b)
    (hYX : ∀ j, ((Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) Y X).atom j).label = a + b)
    (v : Fin (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).size → Coeff (a + b))
    (j : Fin (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) Y X).size) :
    uniformOperator (a + b) _ _ hXY hYX (uniformExchange a b X Y hX hY) v j =
      rowTensorEquiv a b (fun i => (X.atom i).shift) (fun j => (Y.atom j).shift)
        ((objectRowTransport (uniformTensor_eq a b X Y hX hY) (a + b)).symm v)
        (Fin.cast (congrArg Obj.size (uniformTensor_eq b a Y X hY hX)).symm j) := by
  rw [uniformOperator_uniformExchange]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, objectRowTransport_apply]

/-- Read a single output row of the block exchange. -/
theorem rowTensorEquiv_apply {n m : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (v : Fin (rowTensorObject a b p q).size → Coeff (a + b))
    (z : Fin (rowTensorObject b a q p).size) :
    rowTensorEquiv a b p q v z =
      shiftedCommonKernelEquiv a b (p (rowTensorIndex b a q p z).2.1)
        (q (rowTensorIndex b a q p z).1)
        (fun r => v ((rowTensorIndex a b p q).symm
          ((rowTensorIndex b a q p z).2.1, (rowTensorIndex b a q p z).1, r)))
        (rowTensorIndex b a q p z).2.2 := rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
