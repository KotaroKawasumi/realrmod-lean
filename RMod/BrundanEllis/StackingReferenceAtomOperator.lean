import RMod.BrundanEllis.StackingReferenceOperatorTransport
import RMod.BrundanEllis.StackingReferenceTripleRows
import RMod.BrundanEllis.StackingReferenceOuterOperator

/-! The actual exchange of two unshifted atoms is the normalized kernel
operator. Its unit columns will supply the coefficients of the inner
exchange legs after tensoring with a third atom. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT
attribute [local irreducible] uniformOperator Tensor.slotIndexEquiv Tensor.slots

/-- Reindex a binary tensor by its stored fusion row. -/
def atomCoordinates (a b c : ZMod 8) :
    (Fin (atomTensor a b).size → Coeff c) ≃ₗ[ℝ] (FusionTable.Index a b → Coeff c) where
  toFun v r := v ((atomRowIndex a b).symm r)
  invFun v i := v (atomRowIndex a b i)
  left_inv v := by funext i; exact congrArg v ((atomRowIndex a b).symm_apply_apply i)
  right_inv v := by funext r; exact congrArg v ((atomRowIndex a b).apply_symm_apply r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The raw tensor index of singleton factors has two zero endpoint indices. -/
private theorem atom_output_index (a b : ZMod 8) (r : FusionTable.Index a b) :
    rowTensorIndex a b (fun i => ((Obj.singleton (a, 0)).atom i).shift)
      (fun j => ((Obj.singleton (b, 0)).atom j).shift)
      (Fin.cast (congrArg Obj.size (uniformTensor_eq a b (Obj.singleton (a, 0))
        (Obj.singleton (b, 0)) (fun _ => rfl) (fun _ => rfl))).symm
        ((atomRowIndex a b).symm r)) = ((0 : Fin 1), (0 : Fin 1), r) := by
  let e : Fin (atomTensor a b).size ≃
      ((_ : Fin 1) × (_ : Fin 1) × FusionTable.Index a b) :=
    Tensor.slotIndexEquiv realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
  exact congrArg (fun z => (z.1, z.2.1, z.2.2)) (e.apply_symm_apply ⟨0, 0, r⟩)

/-- Reading the input enumeration recovers its fusion row. -/
private theorem atom_input_index (a b : ZMod 8) (r : FusionTable.Index a b) :
    atomRowIndex a b
      (Fin.cast (congrArg Obj.size (uniformTensor_eq a b (Obj.singleton (a, 0))
        (Obj.singleton (b, 0)) (fun _ => rfl) (fun _ => rfl)))
        ((rowTensorIndex a b (fun i => ((Obj.singleton (a, 0)).atom i).shift)
          (fun j => ((Obj.singleton (b, 0)).atom j).shift)).symm
            ((0 : Fin 1), (0 : Fin 1), r))) = r := by
  exact (atomRowIndex a b).apply_symm_apply r

/-- The categorical exchange acts by the normalized reference kernel map. -/
theorem atomUniformExchange_operator (a b : ZMod 8) :
    ((atomCoordinates b a (b + a)).toLinearMap.comp
      (labelOperator (a + b) (b + a) (atomTensor a b) (atomTensor b a)
        (fun _ => rfl) (fun _ => rfl) (add_comm a b)
        (uniformExchange a b (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
          (fun _ => rfl) (fun _ => rfl)))).comp
        (atomCoordinates a b (a + b)).symm.toLinearMap = (normalizedKernelEquiv a b).toLinearMap := by
  apply LinearMap.ext
  intro v
  funext r
  change coefficientCast (add_comm a b)
    (uniformOperator (a + b) _ _ _ _
      (uniformExchange a b (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
        (fun _ => rfl) (fun _ => rfl))
      ((atomCoordinates a b (a + b)).symm v) ((atomRowIndex b a).symm r)) = _
  erw [uniformOperator_uniformExchange_apply a b (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => add_comm b a)]
  erw [rowTensorEquiv_apply, atom_output_index b a r]
  change coefficientCast (add_comm a b)
    (shiftedCommonKernelEquiv a b 0 0
      (fun j => (objectRowTransport _ _).symm ((atomCoordinates a b (a + b)).symm v)
        ((rowTensorIndex a b (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)).symm
          ((0 : Fin 1), (0 : Fin 1), j))) r) = _
  simp only [objectRowTransport_symm_apply]
  change coefficientCast (add_comm a b)
    (shiftedCommonKernelEquiv a b 0 0 (fun j => v (atomRowIndex a b _)) r) = _
  trans coefficientCast (add_comm a b) (shiftedCommonKernelEquiv a b 0 0 v r)
  · apply congrArg (coefficientCast (add_comm a b))
    apply congrArg (fun w => shiftedCommonKernelEquiv a b 0 0 w r)
    funext j
    exact congrArg v (atom_input_index a b j)
  · simp only [shiftedCommonKernelEquiv_apply, commonKernelEquiv_apply, exchangeShift,
      mul_zero, add_zero, (show paritySign (0 : ZMod 2) = (1 : ℝ) from rfl),
      one_smul, coefficientCast_trans]
    rfl

/-- A unit column of the faithful operator is the actual raw coefficient. -/
theorem uniformOperator_unit_column (a : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a)
    (f : Hom realDData X Y) (i : Fin X.size) (j : Fin Y.size) :
    uniformOperator a X Y hX hY f (Pi.single i (Coeff.one a)) j =
      coefficientCast (hX i) ((f i j).coeff ((hX i).trans (hY j).symm)) := by
  rw [uniformOperator_apply]
  have hz (x : Coeff a) : Coeff.mul a x 0 = 0 := by with_unfolding_all exact Coeff.mul_zero a x
  simp only [Pi.single_apply, apply_ite, hz, Coeff.mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- Reindexing retains a single unit column at its fusion position. -/
theorem atomCoordinates_single (a b c : ZMod 8) (i : Fin (atomTensor a b).size) (x : Coeff c) :
    atomCoordinates a b c (Pi.single i x) = Pi.single (atomRowIndex a b i) x := by
  funext r
  simp only [atomCoordinates, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.single_apply, Equiv.symm_apply_eq]

/-- After endpoint transport, each actual exchange coefficient is a kernel unit column. -/
theorem atomUniformExchange_coefficient (a b : ZMod 8)
    (i : Fin (atomTensor a b).size) (j : Fin (atomTensor b a).size) :
    coefficientCast (add_comm a b)
      ((uniformExchange a b (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
        (fun _ => rfl) (fun _ => rfl) i j).coeff (add_comm a b)) =
      normalizedKernelEquiv a b (Pi.single (atomRowIndex a b i) (Coeff.one (a + b)))
        (atomRowIndex b a j) := by
  have h := LinearMap.congr_fun (atomUniformExchange_operator a b)
    (atomCoordinates a b (a + b) (Pi.single i (Coeff.one (a + b))))
  have he := congrArg (fun w => w (atomRowIndex b a j)) h
  dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at he
  rw [LinearEquiv.symm_apply_apply] at he
  change coefficientCast (add_comm a b)
    (uniformOperator (a + b) _ _ _ _
      (uniformExchange a b (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
        (fun _ => rfl) (fun _ => rfl)) (Pi.single i (Coeff.one (a + b)))
      ((atomRowIndex b a).symm (atomRowIndex b a j))) = _ at he
  rw [Equiv.symm_apply_apply, uniformOperator_unit_column] at he
  simp only [atomCoordinates_single, coefficientCast_trans] at he
  exact he

/-- The algebra unit is the stored coefficient basis vector of its unit index. -/
theorem coefficient_one_unit_basis (a : ZMod 8) :
    Coeff.one a = RealPChiKernel.coefficientBasis a (RealPChiKernel.coefficientUnitIndex a) := by
  funext k
  simp [Coeff.one, RealPChiKernel.coefficientBasis, RealPChiKernel.coefficientUnitIndex,
    Fin.ext_iff]

/-- Kernel unit columns are the normalized integer coefficients used by the inner legs. -/
theorem normalizedKernelEquiv_unit (a b : ZMod 8) (r : FusionTable.Index b a)
    (s : FusionTable.Index a b) :
    normalizedKernelEquiv a b (Pi.single s (Coeff.one (a + b))) r =
      normalizingScalar a b • (fun u => (coefficientZ a b (forwardZ a b) r s u.val : ℝ)) := by
  have hv : Pi.single s (Coeff.one (a + b)) =
      (coordinates a b).symm (Pi.single (s, RealPChiKernel.coefficientUnitIndex (a + b)) 1) := by
    funext j
    rw [coordinates_basis]
    simp only [Pi.single_apply, coefficient_one_unit_basis]
  rw [hv]
  funext u
  erw [normalizedKernelEquiv_basis a b (r, u) (s, RealPChiKernel.coefficientUnitIndex (a + b))]
  simp only [coefficientZ, dif_pos u.isLt, Pi.smul_apply, smul_eq_mul]

/-- Closed coefficients of the actual binary exchange, in its original row order. -/
theorem atomUniformExchange_coefficient_real (a b : ZMod 8)
    (i : Fin (atomTensor a b).size) (j : Fin (atomTensor b a).size) :
    coefficientCast (add_comm a b)
      ((uniformExchange a b (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
        (fun _ => rfl) (fun _ => rfl) i j).coeff (add_comm a b)) =
      normalizingScalar a b • (fun u =>
        (coefficientZ a b (forwardZ a b) (atomRowIndex b a j) (atomRowIndex a b i) u.val : ℝ)) :=
  (atomUniformExchange_coefficient a b i j).trans
    (normalizedKernelEquiv_unit a b (atomRowIndex b a j) (atomRowIndex a b i))

end RMod.BrundanEllis.Stacking.ReferenceCommutor
