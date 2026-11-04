import RMod.BrundanEllis.StackingReferenceFamilyRightLinear
import RMod.BrundanEllis.StackingReferenceRowTransport

/-! Identify the reversed tensor action over the common algebra with the given
reference tensor after the equality of endpoint labels. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Reading tensor blocks commutes with coefficient transport. -/
theorem rowTensorCoordinates_cast {n m : ℕ} (a b c d : ZMod 8) (h : c = d)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (v : Fin (rowTensorObject a b p q).size → Coeff c) (i : Fin n) (j : Fin m) :
    rowTensorCoordinates a b p q (Coeff d) (rowCoefficientCast h v) i j =
      rowCoefficientCast h (rowTensorCoordinates a b p q (Coeff c) v i j) := rfl

/-- The reversed action is conjugation of the actual swapped tensor operator. -/
theorem reversedFamilyTensorOperator_conjugate {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) :
    reversedFamilyTensorOperator a b p p' q q' F G =
      (rowCoefficientCast (add_comm b a)).toLinearMap.comp
        ((familyTensorOperator b a q q' p p' G F).comp
          (rowCoefficientCast (add_comm b a)).symm.toLinearMap) := by
  apply LinearMap.ext
  intro v
  apply (rowTensorCoordinates b a q' p' (Coeff (a + b))).injective
  funext j' i'
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, rowTensorCoordinates_cast,
    familyTensorOperator_coordinate, reversedFamilyTensorOperator_coordinate, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- The common-algebra reversed morphism is the equality transport of the actual tensor. -/
theorem reversedFamilyHom_actual {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) :
    reversedFamilyHom a b p p' q q' F G =
      homTransport (rowTensorObject_target a b p q).symm (rowTensorObject_target a b p' q').symm
        (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
          (rowHom b q q' (fun j' j => G j j')) (rowHom a p p' (fun i' i => F i i'))) := by
  unfold reversedFamilyHom
  rw [reversedFamilyTensorOperator_conjugate, rowMatrixOf_conjugate,
    ← rowHom_transport_label, familyTensorOperator_actual]

/-- The actual reference tensor exchange is natural for all homogeneous finite matrices. -/
theorem tensorExchange_naturality {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) (d e : ZMod 2)
    (hF : ∀ i i', (realDData.algebra a).MemGrade (d + p i + p' i') (F i i'))
    (hG : ∀ j j', (realDData.algebra b).MemGrade (e + q j + q' j') (G j j')) :
    Hom.comp
      (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
        (rowHom a p p' (fun i' i => F i i')) (rowHom b q q' (fun j' j => G j j')))
      (tensorExchange a b p' q') =
    Hom.smul (paritySign (degree a b * (d + e) + d * e))
      (Hom.comp (tensorExchange a b p q)
        (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
          (rowHom b q q' (fun j' j => G j j')) (rowHom a p p' (fun i' i => F i i')))) := by
  have h := congrArg (homTransport rfl (rowTensorObject_target a b p' q'))
    (familyExchange_rows_naturality a b p p' q q' F G d e hF hG)
  rw [homTransport_comp rfl rfl, homTransport_smul,
    homTransport_comp rfl (rowTensorObject_target a b p q), reversedFamilyHom_actual,
    homTransport_trans] at h
  exact h

end RMod.BrundanEllis.Stacking.ReferenceCommutor
