import RMod.BrundanEllis.StackingReferenceHexagonMaps
import RMod.BrundanEllis.StackingReferenceOperatorTransport
import RMod.BrundanEllis.StackingReferenceAssociatorOperator
import RMod.BrundanEllis.StackingReferenceOuterOperator

/-! Identify the concrete outer exchange maps of the reference category with
operators on the same two fusion-row coordinates used in the hexagon proof. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT
attribute [local irreducible] uniformOperator Tensor.slotIndexEquiv Tensor.slots

/-- The left-associated output enumeration retains the inner fusion row. -/
private theorem left_exchange_index (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    rowTensorIndex (a + b) c (fun j => ((atomTensor a b).atom j).shift)
      (fun i => ((Obj.singleton (c, 0)).atom i).shift)
      (Fin.cast (congrArg Obj.size (uniformTensor_eq (a + b) c (atomTensor a b)
        (Obj.singleton (c, 0)) (fun _ => rfl) (fun _ => rfl))).symm
        ((leftAtomIndex a b c).symm (r, s))) = ((atomRowIndex a b).symm r, (0 : Fin 1), s) := by
  let e : Fin (leftAtomTensor a b c).size ≃
      ((_ : Fin (atomTensor a b).size) × (_ : Fin 1) × FusionTable.Index (a + b) c) :=
    Tensor.slotIndexEquiv realDData (shiftCData realDData realCData realComputableNuBeta.data)
    (atomTensor a b) (Obj.singleton (c, 0))
  exact congrArg (fun z => (z.1, z.2.1, z.2.2))
    (e.apply_symm_apply ⟨(atomRowIndex a b).symm r, 0, s⟩)

/-- The reverse enumeration reads the original right-associated fusion pair. -/
private theorem right_exchange_index (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    rightAtomIndex a b c
      (Fin.cast (congrArg Obj.size (uniformTensor_eq a (b + c) (Obj.singleton (a, 0))
        (atomTensor b c) (fun _ => rfl) (fun _ => rfl)))
        ((rowTensorIndex a (b + c) (fun i => ((Obj.singleton (a, 0)).atom i).shift)
          (fun j => ((atomTensor b c).atom j).shift)).symm
            ((0 : Fin 1), (atomRowIndex b c).symm r, s))) = (r, s) := by
  exact (rightAtomIndex a b c).apply_symm_apply (r, s)

/-- Right-associated output rows retain the inner fusion row after exchange. -/
private theorem right_exchange_output (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    rowTensorIndex a (b + c) (fun i => ((Obj.singleton (a, 0)).atom i).shift)
      (fun j => ((atomTensor b c).atom j).shift)
      (Fin.cast (congrArg Obj.size (uniformTensor_eq a (b + c) (Obj.singleton (a, 0))
        (atomTensor b c) (fun _ => rfl) (fun _ => rfl))).symm
        ((rightAtomIndex a b c).symm (r, s))) = ((0 : Fin 1), (atomRowIndex b c).symm r, s) := by
  let e : Fin (rightAtomTensor a b c).size ≃
      ((_ : Fin 1) × (_ : Fin (atomTensor b c).size) × FusionTable.Index a (b + c)) :=
    Tensor.slotIndexEquiv realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (Obj.singleton (a, 0)) (atomTensor b c)
  exact congrArg (fun z => (z.1, z.2.1, z.2.2))
    (e.apply_symm_apply ⟨0, (atomRowIndex b c).symm r, s⟩)

/-- Left-associated input rows read the original fusion pair. -/
private theorem left_exchange_input (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    leftAtomIndex a b c
      (Fin.cast (congrArg Obj.size (uniformTensor_eq (a + b) c (atomTensor a b)
        (Obj.singleton (c, 0)) (fun _ => rfl) (fun _ => rfl)))
        ((rowTensorIndex (a + b) c (fun j => ((atomTensor a b).atom j).shift)
          (fun i => ((Obj.singleton (c, 0)).atom i).shift)).symm
            ((atomRowIndex a b).symm r, (0 : Fin 1), s))) = (r, s) := by
  exact (leftAtomIndex a b c).apply_symm_apply (r, s)

/-- A binary atom row has precisely its stored kernel parity. -/
private theorem atomTensor_shift (a b : ZMod 8) (r : FusionTable.Index a b) :
    ((atomTensor a b).atom ((atomRowIndex a b).symm r)).shift = kernelRowParity a b r := by
  with_unfolding_all change 0 + 0 + kernelRowParity a b (atomRowIndex a b ((atomRowIndex a b).symm r)) = _
  rw [Equiv.apply_symm_apply, zero_add, zero_add]

/-- The actual outer-right exchange is the coordinate operator of the first hexagon. -/
theorem outerRightMap_operator (a b c : ZMod 8) :
    ((leftTripleCoordinates b c a).toLinearMap.comp
      (labelOperator (a + b + c) (b + c + a) (rightAtomTensor a b c) (leftAtomTensor b c a)
        (rightAtomTensor_label a b c) (leftAtomTensor_label b c a)
        ((add_assoc a b c).trans (add_comm a (b + c))) (outerRightMap a b c))).comp
        (rightTripleCoordinates a b c).symm.toLinearMap = outerRightOperator a b c := by
  rw [labelOperator_source_cast (add_assoc a b c) (add_comm a (b + c))]
  unfold labelOperator outerRightMap
  apply LinearMap.ext
  intro v
  funext r s
  change coefficientCast (add_comm a (b + c))
    (uniformOperator (a + (b + c)) _ _ _ _
      (uniformExchange a (b + c) (Obj.singleton (a, 0)) (atomTensor b c)
        (fun _ => rfl) (fun _ => rfl))
      (rowCoefficientCast (add_assoc a b c) ((rightTripleCoordinates a b c).symm v))
      ((leftAtomIndex b c a).symm (r, s))) = _
  erw [uniformOperator_uniformExchange_apply a (b + c) (Obj.singleton (a, 0)) (atomTensor b c)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => add_comm (b + c) a)]
  erw [rowTensorEquiv_apply, left_exchange_index b c a r s]
  dsimp only [Prod.fst, Prod.snd]
  erw [atomTensor_shift]
  change coefficientCast (add_comm a (b + c))
    (shiftedCommonKernelEquiv a (b + c) 0 (kernelRowParity b c r)
      (fun j => (objectRowTransport _ _).symm
        (rowCoefficientCast (add_assoc a b c) ((rightTripleCoordinates a b c).symm v))
        ((rowTensorIndex a (b + c) (fun _ : Fin 1 => 0)
          (fun i => ((atomTensor b c).atom i).shift)).symm
            ((0 : Fin 1), (atomRowIndex b c).symm r, j))) s) = _
  simp only [objectRowTransport_symm_apply, rowCoefficientCast_apply]
  change coefficientCast (add_comm a (b + c))
    (shiftedCommonKernelEquiv a (b + c) 0 (kernelRowParity b c r)
      (fun j => coefficientCast (add_assoc a b c)
        (v (rightAtomIndex a b c _).1 (rightAtomIndex a b c _).2)) s) = _
  trans coefficientCast (add_comm a (b + c))
    (shiftedCommonKernelEquiv a (b + c) 0 (kernelRowParity b c r)
      (fun j => coefficientCast (add_assoc a b c) (v r j)) s)
  · apply congrArg (coefficientCast (add_comm a (b + c)))
    apply congrArg (fun w => shiftedCommonKernelEquiv a (b + c) 0 (kernelRowParity b c r) w s)
    funext j
    exact congrArg (fun z : FusionTable.Index b c × FusionTable.Index a (b + c) =>
      coefficientCast (add_assoc a b c) (v z.1 z.2)) (right_exchange_index a b c r j)
  · simp only [shiftedCommonKernelEquiv_apply, Pi.smul_apply, commonKernelEquiv_apply,
      map_smul, coefficientCast_trans]
    rfl

/-- The actual outer-left exchange is the coordinate operator of the second hexagon. -/
theorem outerLeftMap_operator (a b c : ZMod 8) :
    ((rightTripleCoordinates c a b).toLinearMap.comp
      (labelOperator (a + b + c) (c + a + b) (leftAtomTensor a b c) (rightAtomTensor c a b)
        (leftAtomTensor_label a b c) (rightAtomTensor_label c a b)
        ((add_comm (a + b) c).trans (add_assoc c a b).symm) (outerLeftMap a b c))).comp
        (leftTripleCoordinates a b c).symm.toLinearMap = outerLeftOperator a b c := by
  rw [labelOperator_target_cast (add_comm (a + b) c) (add_assoc c a b).symm
    (hY := fun _ => rfl)]
  unfold labelOperator outerLeftMap
  apply LinearMap.ext
  intro v
  funext r s
  change coefficientCast (add_assoc c a b).symm
    (coefficientCast (add_comm (a + b) c)
      (uniformOperator (a + b + c) _ _ _ _
        (uniformExchange (a + b) c (atomTensor a b) (Obj.singleton (c, 0))
          (fun _ => rfl) (fun _ => rfl)) ((leftTripleCoordinates a b c).symm v)
        ((rightAtomIndex c a b).symm (r, s)))) = _
  erw [uniformOperator_uniformExchange_apply (a + b) c (atomTensor a b) (Obj.singleton (c, 0))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => add_comm c (a + b))]
  erw [rowTensorEquiv_apply, right_exchange_output c a b r s]
  dsimp only [Prod.fst, Prod.snd]
  erw [atomTensor_shift]
  change coefficientCast (add_assoc c a b).symm
    (coefficientCast (add_comm (a + b) c)
      (shiftedCommonKernelEquiv (a + b) c (kernelRowParity a b r) 0
        (fun j => (objectRowTransport _ _).symm ((leftTripleCoordinates a b c).symm v)
          ((rowTensorIndex (a + b) c (fun i => ((atomTensor a b).atom i).shift)
            (fun _ : Fin 1 => 0)).symm ((atomRowIndex a b).symm r, (0 : Fin 1), j))) s)) = _
  simp only [objectRowTransport_symm_apply]
  change coefficientCast (add_assoc c a b).symm
    (coefficientCast (add_comm (a + b) c)
      (shiftedCommonKernelEquiv (a + b) c (kernelRowParity a b r) 0
        (fun j => v (leftAtomIndex a b c _).1 (leftAtomIndex a b c _).2) s)) = _
  trans coefficientCast (add_assoc c a b).symm
    (coefficientCast (add_comm (a + b) c)
      (shiftedCommonKernelEquiv (a + b) c (kernelRowParity a b r) 0 (v r) s))
  · apply congrArg (coefficientCast (add_assoc c a b).symm)
    apply congrArg (coefficientCast (add_comm (a + b) c))
    apply congrArg (fun w => shiftedCommonKernelEquiv (a + b) c (kernelRowParity a b r) 0 w s)
    funext j
    exact congrArg (fun z : FusionTable.Index a b × FusionTable.Index (a + b) c =>
      v z.1 z.2) (left_exchange_input a b c r j)
  · simp only [shiftedCommonKernelEquiv_apply, Pi.smul_apply, commonKernelEquiv_apply,
      map_smul, coefficientCast_trans]
    simp only [outerLeftOperator, shiftedExchange, LinearMap.smul_apply, LinearEquiv.coe_coe,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, map_smul]
    rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
