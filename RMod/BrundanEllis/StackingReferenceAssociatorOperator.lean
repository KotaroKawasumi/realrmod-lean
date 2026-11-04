import RMod.BrundanEllis.StackingReferenceTripleRows
import RMod.BrundanEllis.StackingReferenceUniformOperator

/-! The actual reference associator, acting on its free right-module rows,
is the normalized connector operator. Thus its previously verified real
matrix represents the categorical associator itself. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Left-associated row coordinates retain both internal fusion indices. -/
def leftTripleCoordinates (a b c : ZMod 8) :
    (Fin (leftAtomTensor a b c).size → Coeff (a + b + c)) ≃ₗ[ℝ] LeftCarrier a b c where
  toFun v r s := v ((leftAtomIndex a b c).symm (r, s))
  invFun v i := v (leftAtomIndex a b c i).1 (leftAtomIndex a b c i).2
  left_inv v := by funext i; change v ((leftAtomIndex a b c).symm (leftAtomIndex a b c i)) = _; rw [Equiv.symm_apply_apply]
  right_inv v := by funext r s; dsimp only; rw [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Right-associated row coordinates use the same endpoint division algebra. -/
def rightTripleCoordinates (a b c : ZMod 8) :
    (Fin (rightAtomTensor a b c).size → Coeff (a + b + c)) ≃ₗ[ℝ] RightCarrier a b c where
  toFun v r s := v ((rightAtomIndex a b c).symm (r, s))
  invFun v i := v (rightAtomIndex a b c i).1 (rightAtomIndex a b c i).2
  left_inv v := by funext i; change v ((rightAtomIndex a b c).symm (rightAtomIndex a b c i)) = _; rw [Equiv.symm_apply_apply]
  right_inv v := by funext r s; dsimp only; rw [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem coefficientRawFinSum {a : ZMod 8} {n : ℕ} (f : Fin n → Coeff a) :
    CData.rawFinSum (realDData.algebra a) f = ∑ i, f i := by
  change (List.ofFn f).sum = ∑ i, f i
  exact List.sum_ofFn

/-- The coordinate operator comes from the actual categorical associator. -/
theorem atomAssociator_operator (a b c : ZMod 8) :
    ((rightTripleCoordinates a b c).toLinearMap.comp
      (uniformOperator (a + b + c) (leftAtomTensor a b c) (rightAtomTensor a b c)
        (leftAtomTensor_label a b c) (rightAtomTensor_label a b c)
        (RealAssociator.hom (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0))))).comp
        (leftTripleCoordinates a b c).symm.toLinearMap = associatorOperator a b c := by
  apply LinearMap.ext
  intro v
  funext t u
  dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe, rightTripleCoordinates, LinearMap.coe_mk, AddHom.coe_mk]
  erw [uniformOperator_apply, associatorOperator_coefficients]
  with_unfolding_all simp_rw [atom_associator_coefficient]
  simp only [Equiv.apply_symm_apply, coefficientRawFinSum]
  change (∑ i : Fin (leftAtomTensor a b c).size,
      Coeff.mul (a + b + c)
        (Associator.homCoefficient realComputableShiftedRawDCT.data a b c
          (leftAtomIndex a b c i).1 (leftAtomIndex a b c i).2 t u)
        (v (leftAtomIndex a b c i).1 (leftAtomIndex a b c i).2)) = _
  let w := fun rs : FusionTable.Index a b × FusionTable.Index (a + b) c =>
    Coeff.mul (a + b + c)
      (Associator.homCoefficient realComputableShiftedRawDCT.data a b c rs.1 rs.2 t u)
      (v rs.1 rs.2)
  exact (Equiv.sum_comp (leftAtomIndex a b c) w).trans (Fintype.sum_prod_type w)

end RMod.BrundanEllis.Stacking.ReferenceCommutor
