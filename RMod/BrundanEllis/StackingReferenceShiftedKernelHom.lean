import RMod.BrundanEllis.StackingReferenceAtomExchange
import RMod.BrundanEllis.StackingReferenceShiftedExchange

/-! Extend the actual reference exchange to all parity shifts of singleton
atoms. Forward and inverse maps are constructed from the same normalized
right-module equivalence; their grades and inverse laws are then transported
to the actual raw tensor objects. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Multiplication by a real scalar preserves a homogeneous row vector. -/
theorem rowGrade_smul {n : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (d : ZMod 2)
    (r : ℝ) (v : Fin n → Coeff a) (hv : RowGrade a p d v) : RowGrade a p d (r • v) := by
  intro i
  change (realDData.algebra a).component (d + p i) (r • v i) = r • v i
  have h : (realDData.algebra a).component (d + p i) (r • v i) =
      r • (realDData.algebra a).component (d + p i) (v i) :=
    (realDLaws.algebra_laws a).component_smul (d + p i) r (v i)
  exact h.trans (congrArg (fun x : Coeff a => r • x) (hv i))

/-- The strict right action is real-linear in its module argument. -/
theorem rowRight_smul {n : ℕ} (a : ZMod 8) (r : ℝ) (v : Fin n → Coeff a) (x : Coeff a) :
    rowRight a (r • v) x = r • rowRight a v x := by
  funext i
  with_unfolding_all exact Coeff.smul_mul a r (v i) x

private theorem paritySign_ne_zero (p : ZMod 2) : paritySign p ≠ 0 := by
  rw [paritySign_pow]
  exact pow_ne_zero _ (by norm_num)

/-- Include the endpoint parity correction in the common-algebra equivalence. -/
def shiftedCommonKernelEquiv (a b : ZMod 8) (p q : ZMod 2) :
    RealCCarrier a b ≃ₗ[ℝ] (FusionTable.Index b a → Coeff (a + b)) :=
  (commonKernelEquiv a b).trans
    (LinearEquiv.smulOfNeZero ℝ _ (paritySign (exchangeShift a b p q)) (paritySign_ne_zero _))

@[simp] theorem shiftedCommonKernelEquiv_apply (a b : ZMod 8) (p q : ZMod 2) (v : RealCCarrier a b) :
    shiftedCommonKernelEquiv a b p q v = paritySign (exchangeShift a b p q) • commonKernelEquiv a b v := rfl

/-- The real scalar correction still commutes with every right coefficient. -/
theorem shiftedCommonKernelEquiv_right (a b : ZMod 8) (p q : ZMod 2)
    (v : RealCCarrier a b) (x : Coeff (a + b)) :
    shiftedCommonKernelEquiv a b p q (rowRight (a + b) v x) =
      rowRight (a + b) (shiftedCommonKernelEquiv a b p q v) x := by
  simp only [shiftedCommonKernelEquiv_apply, commonKernelEquiv_right, rowRight_smul]

/-- Shifting both endpoints changes vector degrees by their total parity. -/
theorem shiftedCommonKernelEquiv_grade (a b : ZMod 8) (p q d : ZMod 2) (v : RealCCarrier a b)
    (hv : RowGrade (a + b) (fun i => p + q + kernelRowParity a b i) d v) :
    RowGrade (a + b) (fun i => q + p + kernelRowParity b a i) (d + degree a b)
      (shiftedCommonKernelEquiv a b p q v) := by
  have hsource : RowGrade (a + b) (kernelRowParity a b) (d + p + q) v := by
    simpa only [RowGrade, add_assoc] using hv
  have h := rowGrade_smul (a + b) (kernelRowParity b a) _
    (paritySign (exchangeShift a b p q)) _ (commonKernelEquiv_grade a b _ _ hsource)
  simpa only [shiftedCommonKernelEquiv_apply, RowGrade, add_assoc, add_comm, add_left_comm] using h

/-- The inverse has the same homogeneous degree. -/
theorem shiftedCommonKernelEquiv_symm_grade (a b : ZMod 8) (p q d : ZMod 2)
    (v : FusionTable.Index b a → Coeff (a + b))
    (hv : RowGrade (a + b) (fun i => q + p + kernelRowParity b a i) d v) :
    RowGrade (a + b) (fun i => p + q + kernelRowParity a b i) (d + degree a b)
      ((shiftedCommonKernelEquiv a b p q).symm v) := by
  have hsource : RowGrade (a + b) (kernelRowParity b a) (d + q + p) v := by
    simpa only [RowGrade, add_assoc] using hv
  have h := commonKernelEquiv_symm_grade a b _ _
    (rowGrade_smul (a + b) (kernelRowParity b a) _ (paritySign (exchangeShift a b p q))⁻¹ _ hsource)
  change RowGrade (a + b) (fun i => p + q + kernelRowParity a b i) (d + degree a b)
    ((commonKernelEquiv a b).symm ((paritySign (exchangeShift a b p q))⁻¹ • v))
  simpa only [RowGrade, add_assoc, add_comm, add_left_comm] using h

/-- The actual tensor product of arbitrary shifted singleton atoms. -/
def shiftedAtomTensor (a b : ZMod 8) (p q : ZMod 2) : Obj :=
  Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)
    (Obj.singleton (a, p)) (Obj.singleton (b, q))

theorem shiftedAtomTensor_source (a b : ZMod 8) (p q : ZMod 2) :
    rowObject (a + b) (fun i => p + q + kernelRowParity a b i) = shiftedAtomTensor a b p q :=
  (tensorAtom_rowObject a b p q).symm

theorem shiftedAtomTensor_target (a b : ZMod 8) (p q : ZMod 2) :
    rowObject (a + b) (fun i => q + p + kernelRowParity b a i) = shiftedAtomTensor b a q p := by
  rw [← shiftedAtomTensor_source, add_comm a b]

/-- The exchange on shifted atoms, as an actual raw morphism. -/
def shiftedAtomExchange (a b : ZMod 8) (p q : ZMod 2) :
    Hom realDData (shiftedAtomTensor a b p q) (shiftedAtomTensor b a q p) :=
  homTransport (shiftedAtomTensor_source a b p q) (shiftedAtomTensor_target a b p q)
    (rowHom (a + b) _ _ (rowMatrixOf (a + b) (shiftedCommonKernelEquiv a b p q).toLinearMap))

/-- The actual inverse is read from the inverse right-module map. -/
def shiftedAtomExchangeInv (a b : ZMod 8) (p q : ZMod 2) :
    Hom realDData (shiftedAtomTensor b a q p) (shiftedAtomTensor a b p q) :=
  homTransport (shiftedAtomTensor_target a b p q) (shiftedAtomTensor_source a b p q)
    (rowHom (a + b) _ _ (rowMatrixOf (a + b) (shiftedCommonKernelEquiv a b p q).symm.toLinearMap))

theorem shiftedAtomExchange_grade (a b : ZMod 8) (p q : ZMod 2) :
    Hom.MemGrade (degree a b) (shiftedAtomExchange a b p q) :=
  homTransport_grade _ _ _ _ (rowHom_matrixOf_grade (a + b) _ _ _ _
    (shiftedCommonKernelEquiv_grade a b p q))

theorem shiftedAtomExchangeInv_grade (a b : ZMod 8) (p q : ZMod 2) :
    Hom.MemGrade (degree a b) (shiftedAtomExchangeInv a b p q) :=
  homTransport_grade _ _ _ _ (rowHom_matrixOf_grade (a + b) _ _ _ _
    (shiftedCommonKernelEquiv_symm_grade a b p q))

theorem shiftedAtomExchange_inverse (a b : ZMod 8) (p q : ZMod 2) :
    Hom.comp (shiftedAtomExchange a b p q) (shiftedAtomExchangeInv a b p q) =
        Hom.id realDData (shiftedAtomTensor a b p q) ∧
      Hom.comp (shiftedAtomExchangeInv a b p q) (shiftedAtomExchange a b p q) =
        Hom.id realDData (shiftedAtomTensor b a q p) := by
  have h := rowHom_equiv_inverse (a + b) (fun i => p + q + kernelRowParity a b i)
    (fun i => q + p + kernelRowParity b a i) (shiftedCommonKernelEquiv a b p q)
    (shiftedCommonKernelEquiv_right a b p q)
  exact homTransport_inverse _ _ _ _ h.1 h.2

example : Hom.MemGrade 1 (shiftedAtomExchange 1 1 1 0) := shiftedAtomExchange_grade 1 1 1 0

example : Hom.comp (shiftedAtomExchange 1 4 1 1) (shiftedAtomExchangeInv 1 4 1 1) =
    Hom.id realDData (shiftedAtomTensor 1 4 1 1) := (shiftedAtomExchange_inverse 1 4 1 1).1

end RMod.BrundanEllis.Stacking.ReferenceCommutor
