import RMod.BrundanEllis.StackingReferenceTensorRows
import RMod.BrundanEllis.StackingReferenceAssociatorColumns
import Superfusion.RMod.FromRawDCT.RealAssociator

/-! The two ternary coefficient index sets are the actual rows of the
threefold tensor of unshifted atoms. The equivalences retain the stored
lexicographic enumeration, so later matrix comparisons detect raw maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Actual left-associated tensor of three unshifted reference atoms. -/
def leftAtomTensor (a b c : ZMod 8) : Obj :=
  Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)
    (atomTensor a b) (Obj.singleton (c, 0))

/-- Actual right-associated tensor of the same three atoms. -/
def rightAtomTensor (a b c : ZMod 8) : Obj :=
  Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)
    (Obj.singleton (a, 0)) (atomTensor b c)

/-- The row index of an actual tensor of two unshifted atoms. -/
def atomRowIndex (a b : ZMod 8) : Fin (atomTensor a b).size ≃ FusionTable.Index a b := by
  let e : Fin (atomTensor a b).size ≃ ((_ : Fin 1) × (_ : Fin 1) × FusionTable.Index a b) :=
    Tensor.slotIndexEquiv realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
  exact e.trans ((Equiv.sigmaEquivProd _ _).trans
    ((Equiv.uniqueProd _ _).trans ((Equiv.sigmaEquivProd _ _).trans (Equiv.uniqueProd _ _))))

/-- The two internal fusion indices on the left route. -/
def leftAtomIndex (a b c : ZMod 8) :
    Fin (leftAtomTensor a b c).size ≃
      FusionTable.Index a b × FusionTable.Index (a + b) c := by
  let e : Fin (leftAtomTensor a b c).size ≃
      ((_ : Fin (atomTensor a b).size) × (_ : Fin 1) × FusionTable.Index (a + b) c) :=
    Tensor.slotIndexEquiv realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (atomTensor a b) (Obj.singleton (c, 0))
  exact e.trans ((Equiv.sigmaEquivProd _ _).trans
    (Equiv.prodCongr (atomRowIndex a b)
      ((Equiv.sigmaEquivProd _ _).trans (Equiv.uniqueProd _ _))))

set_option maxHeartbeats 1000000 in
/-- The two internal fusion indices on the right route. -/
def rightAtomIndex (a b c : ZMod 8) :
    Fin (rightAtomTensor a b c).size ≃
      FusionTable.Index b c × FusionTable.Index a (b + c) := by
  let e : Fin (rightAtomTensor a b c).size ≃
      ((_ : Fin 1) × (_ : Fin (atomTensor b c).size) × FusionTable.Index a (b + c)) :=
    Tensor.slotIndexEquiv realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (Obj.singleton (a, 0)) (atomTensor b c)
  exact e.trans ((Equiv.sigmaEquivProd _ _).trans
    ((Equiv.uniqueProd _ _).trans ((Equiv.sigmaEquivProd _ _).trans
      (Equiv.prodCongr (atomRowIndex b c) (Equiv.refl _)))))

/-- Every left-associated row has the sum of the three labels. -/
theorem leftAtomTensor_label (a b c : ZMod 8) (i : Fin (leftAtomTensor a b c).size) :
    ((leftAtomTensor a b c).atom i).label = a + b + c := rfl

/-- The corresponding right label differs only by reassociation of addition. -/
theorem rightAtomTensor_label (a b c : ZMod 8) (i : Fin (rightAtomTensor a b c).size) :
    ((rightAtomTensor a b c).atom i).label = a + b + c := (add_assoc a b c).symm

/-- At unshifted endpoints the explicit endpoint normalization is one. -/
theorem atom_associator_endpoint (a b c : ZMod 8)
    (i : Fin (leftAtomTensor a b c).size) :
    RealAssociator.endpointSign (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
      (Obj.singleton (c, 0))
      ((Tensor.slots realDData (shiftCData realDData realCData realComputableNuBeta.data)
        (atomTensor a b) (Obj.singleton (c, 0))).get i) = 1 := by
  unfold RealAssociator.endpointSign
  change paritySign (_ * 0) = 1
  rw [mul_zero]
  rfl

attribute [local irreducible] Associator.homCoefficient Tensor.slots

set_option maxHeartbeats 4000000 in
/-- The actual atom associator entry is the stored connector coefficient. -/
theorem atom_associator_coefficient (a b c : ZMod 8)
    (i : Fin (leftAtomTensor a b c).size) (j : Fin (rightAtomTensor a b c).size) :
    (RealAssociator.hom (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
      (Obj.singleton (c, 0)) i j).coeff (add_assoc a b c) =
    Associator.homCoefficient realComputableShiftedRawDCT.data a b c
      (leftAtomIndex a b c i).1 (leftAtomIndex a b c i).2
      (rightAtomIndex a b c j).1 (rightAtomIndex a b c j).2 := by
  change (RealAssociator.homEntry _ _ _ _ _).coeff _ = _
  rw [RealAssociator.homEntry, AtomHom.coeff_smul]
  erw [atom_associator_endpoint]
  change (1 : ℝ) • (_ : Coeff (a + b + c)) = _
  rw [one_smul]
  letI : Subsingleton (Fin (Obj.singleton (a, 0)).size) := inferInstanceAs (Subsingleton (Fin 1))
  letI : Subsingleton (Fin (Obj.singleton (b, 0)).size) := inferInstanceAs (Subsingleton (Fin 1))
  letI : Subsingleton (Fin (Obj.singleton (c, 0)).size) := inferInstanceAs (Subsingleton (Fin 1))
  unfold Associator.homEntry
  rw [dif_pos (Subsingleton.elim _ _), dif_pos (Subsingleton.elim _ _),
    dif_pos (Subsingleton.elim _ _), AtomHom.coeff_ofLabelEq]
  change Associator.homCoefficient realComputableShiftedRawDCT.data a b c _ _ _ _ = _
  congr 1

/-- The unit column of the normalized integer matrix is the actual reference entry. -/
theorem atom_associator_coefficient_real (a b c : ZMod 8)
    (i : Fin (leftAtomTensor a b c).size) (j : Fin (rightAtomTensor a b c).size)
    (k : Fin (realRepDim (a + b + c).val)) :
    ((RealAssociator.hom (Obj.singleton (a, 0)) (Obj.singleton (b, 0))
      (Obj.singleton (c, 0)) i j).coeff (add_assoc a b c)) k =
      (associatorScale a b c : ℝ) *
        (associatorZ a b c ((rightAtomIndex a b c j).1, (rightAtomIndex a b c j).2, k)
          ((leftAtomIndex a b c i).1, (leftAtomIndex a b c i).2,
            RealPChiKernel.coefficientUnitIndex (a + b + c)) : ℝ) := by
  exact (congrFun (atom_associator_coefficient a b c i j) k).trans
    (associator_coefficient a b c _ _ _ _ k)

end RMod.BrundanEllis.Stacking.ReferenceCommutor
