import RMod.BrundanEllis.StackingReferenceCommutorData
import RMod.BrundanEllis.StackingMatrixGrade
import Superfusion.RMod.RawDCT.RealComputableShift

/-! Coordinates and actual grading of the real shifted fusion kernels. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

/-- Flatten the row and coefficient indices without changing their order. -/
def coordinates (a b : ZMod 8) : RealCCarrier a b ≃ₗ[ℝ] (Index a b → ℝ) where
  toFun v i := v i.1 i.2
  invFun v r k := v (r, k)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate support describes precisely the grading of the stored kernel. -/
theorem grade_iff (a b : ZMod 8) (d : ZMod 2) (v : RealCCarrier a b) :
    realComputableShiftedRawDCT.data.C.MemGrade a b d v ↔
      CoordinateGrade (parity a b) d (coordinates a b v) := by
  have hp (i : Index a b) :
      realRepBasisParity (a + b) i.2 =
          (d + shiftNu realComputableNuBeta.data a b) + FusionTable.indexParity a b i.1 ↔
        parity a b i = d := by
    dsimp [parity, shiftNu]
    constructor <;> intro h <;>
      linear_combination (norm := (ring_nf; simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero, sub_zero, neg_zero])) h
  constructor
  · intro h i hi
    have h' := congrArg (fun w => w i.1 i.2) h
    change (if realRepBasisParity (a + b) i.2 =
      (d + shiftNu realComputableNuBeta.data a b) + FusionTable.indexParity a b i.1
      then v i.1 i.2 else 0) = v i.1 i.2 at h'
    rw [if_neg (fun he => hi ((hp i).mp he))] at h'
    exact h'.symm
  · intro h
    funext r k
    change (if realRepBasisParity (a + b) k =
      (d + shiftNu realComputableNuBeta.data a b) + FusionTable.indexParity a b r
      then v r k else 0) = v r k
    split_ifs with he
    · rfl
    · exact (h (r, k) (fun he' => he ((hp (r, k)).mpr he'))).symm


/-- The actual left action, with the two input coefficients fixed. -/
def leftOperator (a b : ZMod 8) (x : Coeff a) (y : Coeff b) :
    RealCCarrier a b →ₗ[ℝ] RealCCarrier a b where
  toFun := realComputableShiftedRawDCT.data.C.left a b x y
  map_add' v w := realComputableShiftedRawDCT.laws.C.left_add_module a b x y v w
  map_smul' r v := realComputableShiftedRawDCT.laws.C.left_smul_module a b r x y v

private theorem basis_mem (a : ZMod 8) (k : Fin (realRepDim a.val)) :
    (realDData.algebra a).MemGrade (realRepBasisParity a k)
      (RealPChiKernel.coefficientBasis a k) := by
  apply (Coeff.component_eq_self_iff _ _ _).mpr
  intro j hj
  simp only [RealPChiKernel.coefficientBasis]
  exact if_neg (fun h => hj (congrArg (realRepBasisParity a) h))

theorem paritySign_pow (d : ZMod 2) : paritySign d = (-1 : ℝ) ^ d.val := by
  rcases zmod2_cases d with rfl | rfl
  · rfl
  · change (-1 : ℝ) = (-1 : ℝ) ^ 1
    rw [pow_one]

/-- The actual parity twist on a canonical homogeneous coefficient. -/
theorem twist_basis (a : ZMod 8) (k : Fin (realRepDim a.val)) (p : ZMod 2) :
    routeRowTwist realDData a p (RealPChiKernel.coefficientBasis a k) =
      ((-1 : ℝ) ^ (p * realRepBasisParity a k).val) • RealPChiKernel.coefficientBasis a k := by
  have h := routeRowTwist_of_memGrade (realDData.algebra a) (realDLaws.algebra_laws a)
    p (realRepBasisParity a k) (RealPChiKernel.coefficientBasis a k) (basis_mem a k)
  change routeRowTwist realDData a p (RealPChiKernel.coefficientBasis a k) =
    Coeff.smul a (paritySign (p * realRepBasisParity a k)) (RealPChiKernel.coefficientBasis a k) at h
  rw [paritySign_pow] at h
  funext j
  exact congrFun h j

private theorem unit_basis (a : ZMod 8) :
    Coeff.one a = RealPChiKernel.coefficientBasis a (RealPChiKernel.coefficientUnitIndex a) := by
  funext k
  simp [Coeff.one, RealPChiKernel.coefficientBasis, RealPChiKernel.coefficientUnitIndex,
    Fin.ext_iff]

theorem coordinates_basis (a b : ZMod 8) (s : Index a b) (r : FusionTable.Index a b) :
    (coordinates a b).symm (Pi.single s 1) r =
      if r = s.1 then RealPChiKernel.coefficientBasis (a + b) s.2 else 0 := by
  rcases s with ⟨s, j⟩
  funext k
  by_cases hr : r = s
  · subst r
    simp [coordinates, Pi.single_apply, RealPChiKernel.coefficientBasis]
  · simp [coordinates, hr]

/-- The frozen slot matrix is the actual raw action on every coordinate basis vector. -/
theorem raw_left_basis (a b : ZMod 8) (k : Fin (realRepDim a.val)) (r s : Index a b) :
    coordinates a b
      (realCLeft a b (RealPChiKernel.coefficientBasis a k) (Coeff.one b)
        ((coordinates a b).symm (Pi.single s 1))) r =
      (RealPChiKernel.fusionLeftSlotCoeff a b k.val r.1.val r.2.val s.1.val s.2.val : ℝ) := by
  change ((List.ofFn fun j : FusionTable.Index a b =>
    Coeff.mul (a + b)
      (FusionTable.fusionCoefficient a b r.1 j (RealPChiKernel.coefficientBasis a k) (Coeff.one b))
      ((coordinates a b).symm (Pi.single s 1) j)).sum) r.2 = _
  rw [List.sum_ofFn]
  simp_rw [coordinates_basis]
  have hz (x : Coeff (a + b)) : Coeff.mul (a + b) x 0 = 0 := by
    with_unfolding_all exact Coeff.mul_zero (a + b) x
  simp only [apply_ite, hz, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [unit_basis]
  exact (RealPChiKernel.fusionLeftSlotCoeff_cast a b k r.1 s.1 r.2 s.2).symm

/-- The frozen second-slot matrix is likewise the actual raw action. -/
theorem raw_right_basis (a b : ZMod 8) (k : Fin (realRepDim b.val)) (r s : Index a b) :
    coordinates a b
      (realCLeft a b (Coeff.one a) (RealPChiKernel.coefficientBasis b k)
        ((coordinates a b).symm (Pi.single s 1))) r =
      (RealPChiKernel.fusionRightSlotCoeff a b k.val r.1.val r.2.val s.1.val s.2.val : ℝ) := by
  change ((List.ofFn fun j : FusionTable.Index a b =>
    Coeff.mul (a + b)
      (FusionTable.fusionCoefficient a b r.1 j (Coeff.one a) (RealPChiKernel.coefficientBasis b k))
      ((coordinates a b).symm (Pi.single s 1) j)).sum) r.2 = _
  rw [List.sum_ofFn]
  simp_rw [coordinates_basis]
  have hz (x : Coeff (a + b)) : Coeff.mul (a + b) x 0 = 0 := by
    with_unfolding_all exact Coeff.mul_zero (a + b) x
  simp only [apply_ite, hz, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [unit_basis]
  exact (RealPChiKernel.fusionRightSlotCoeff_cast a b k r.1 s.1 r.2 s.2).symm

private theorem twist_one (a : ZMod 8) (p : ZMod 2) :
    routeRowTwist realDData a p (Coeff.one a) = Coeff.one a := by
  exact routeRowTwist_one (realDData.algebra a) (realDLaws.algebra_laws a) p

/-- The first-slot matrix includes exactly the reference's fixed parity twist. -/
theorem shifted_left_basis (a b : ZMod 8) (k : Fin (realRepDim a.val)) (r s : Index a b) :
    coordinates a b
      (leftOperator a b (RealPChiKernel.coefficientBasis a k) (Coeff.one b)
        ((coordinates a b).symm (Pi.single s 1))) r = (leftAction a b k r s : ℝ) := by
  change coordinates a b (realCLeft a b
    (routeRowTwist realDData a (shiftNu realComputableNuBeta.data a b)
      (RealPChiKernel.coefficientBasis a k))
    (routeRowTwist realDData b (shiftNu realComputableNuBeta.data a b) (Coeff.one b))
    ((coordinates a b).symm (Pi.single s 1))) r = _
  rw [twist_basis, twist_one]
  have hs (c : ℝ) (x : Coeff a) (y : Coeff b) (v : RealCCarrier a b) :
      realCLeft a b (c • x) y v = c • realCLeft a b x y v := by
    with_unfolding_all exact realCLaws.left_smul_left a b c x y v
  rw [hs, map_smul]
  change ((-1 : ℝ) ^ _) * coordinates a b (realCLeft a b _ _ _) r = _
  rw [raw_left_basis]
  simp [leftAction, leftActionZ, shiftNu]

/-- The second-slot matrix uses the same parity twist. -/
theorem shifted_right_basis (a b : ZMod 8) (k : Fin (realRepDim b.val)) (r s : Index a b) :
    coordinates a b
      (leftOperator a b (Coeff.one a) (RealPChiKernel.coefficientBasis b k)
        ((coordinates a b).symm (Pi.single s 1))) r = (rightAction a b k r s : ℝ) := by
  change coordinates a b (realCLeft a b
    (routeRowTwist realDData a (shiftNu realComputableNuBeta.data a b) (Coeff.one a))
    (routeRowTwist realDData b (shiftNu realComputableNuBeta.data a b)
      (RealPChiKernel.coefficientBasis b k))
    ((coordinates a b).symm (Pi.single s 1))) r = _
  rw [twist_basis, twist_one]
  have hs (c : ℝ) (x : Coeff a) (y : Coeff b) (v : RealCCarrier a b) :
      realCLeft a b x (c • y) v = c • realCLeft a b x y v := by
    with_unfolding_all exact realCLaws.left_smul_right a b c x y v
  rw [hs, map_smul]
  change ((-1 : ℝ) ^ _) * coordinates a b (realCLeft a b _ _ _) r = _
  rw [raw_right_basis]
  simp [rightAction, rightActionZ, shiftNu]

/-- Basis agreement determines the complete first-slot real linear operator. -/
theorem leftAction_actual (a b : ZMod 8) (k : Fin (realRepDim a.val)) :
    ((coordinates a b).toLinearMap.comp
      (leftOperator a b (RealPChiKernel.coefficientBasis a k) (Coeff.one b))).comp
        (coordinates a b).symm.toLinearMap =
      ((leftAction a b k).map ((↑) : ℚ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (Index a b)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  change coordinates a b (leftOperator a b _ _
    ((coordinates a b).symm (Pi.single s 1))) r =
      (((leftAction a b k).map ((↑) : ℚ → ℝ)).mulVec (Pi.single s 1)) r
  rw [Matrix.mulVec_single_one]
  exact shifted_left_basis a b k r s

/-- Basis agreement also determines the complete second-slot operator. -/
theorem rightAction_actual (a b : ZMod 8) (k : Fin (realRepDim b.val)) :
    ((coordinates a b).toLinearMap.comp
      (leftOperator a b (Coeff.one a) (RealPChiKernel.coefficientBasis b k))).comp
        (coordinates a b).symm.toLinearMap =
      ((rightAction a b k).map ((↑) : ℚ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (Index a b)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  change coordinates a b (leftOperator a b _ _
    ((coordinates a b).symm (Pi.single s 1))) r =
      (((rightAction a b k).map ((↑) : ℚ → ℝ)).mulVec (Pi.single s 1)) r
  rw [Matrix.mulVec_single_one]
  exact shifted_right_basis a b k r s

/-- Evaluation form of the first-slot comparison, for arbitrary kernel vectors. -/
theorem leftAction_apply (a b : ZMod 8) (k : Fin (realRepDim a.val)) (v : RealCCarrier a b) :
    coordinates a b (leftOperator a b (RealPChiKernel.coefficientBasis a k) (Coeff.one b) v) =
      ((leftAction a b k).map ((↑) : ℚ → ℝ)).mulVec (coordinates a b v) := by
  have h := LinearMap.congr_fun (leftAction_actual a b k) (coordinates a b v)
  change coordinates a b (leftOperator a b _ _ ((coordinates a b).symm (coordinates a b v))) = _ at h
  simpa only [LinearEquiv.symm_apply_apply, Matrix.mulVecLin_apply] using h

/-- Evaluation form for the second slot. -/
theorem rightAction_apply (a b : ZMod 8) (k : Fin (realRepDim b.val)) (v : RealCCarrier a b) :
    coordinates a b (leftOperator a b (Coeff.one a) (RealPChiKernel.coefficientBasis b k) v) =
      ((rightAction a b k).map ((↑) : ℚ → ℝ)).mulVec (coordinates a b v) := by
  have h := LinearMap.congr_fun (rightAction_actual a b k) (coordinates a b v)
  change coordinates a b (leftOperator a b _ _ ((coordinates a b).symm (coordinates a b v))) = _ at h
  simpa only [LinearEquiv.symm_apply_apply, Matrix.mulVecLin_apply] using h

/-- Linearity in the first input coefficient of the actual action. -/
def firstInput (a b : ZMod 8) (y : Coeff b) (v : RealCCarrier a b) :
    Coeff a →ₗ[ℝ] RealCCarrier a b where
  toFun x := leftOperator a b x y v
  map_add' x x' := realComputableShiftedRawDCT.laws.C.left_add_left a b x x' y v
  map_smul' c x := realComputableShiftedRawDCT.laws.C.left_smul_left a b c x y v

/-- Linearity in the second input coefficient. -/
def secondInput (a b : ZMod 8) (x : Coeff a) (v : RealCCarrier a b) :
    Coeff b →ₗ[ℝ] RealCCarrier a b where
  toFun y := leftOperator a b x y v
  map_add' y y' := realComputableShiftedRawDCT.laws.C.left_add_right a b x y y' v
  map_smul' c y := realComputableShiftedRawDCT.laws.C.left_smul_right a b c x y v

/-- The stored canonical coefficient basis is the ordinary coordinate basis. -/
theorem coefficientBasis_single (a : ZMod 8) (k : Fin (realRepDim a.val)) :
    RealPChiKernel.coefficientBasis a k = Pi.single k 1 := by
  funext j
  simp [RealPChiKernel.coefficientBasis, Pi.single_apply]

/-- The two separate input actions compose to the given binary action. -/
theorem leftOperator_factor (a b : ZMod 8) (x : Coeff a) (y : Coeff b) (v : RealCCarrier a b) :
    leftOperator a b x (Coeff.one b) (leftOperator a b (Coeff.one a) y v) =
      leftOperator a b x y v := by
  have h := realComputableShiftedRawDCT.laws.C.left_mul a b 0 0
    x (Coeff.one a) (Coeff.one b) y v
    (realDLaws.algebra_laws b).one_mem (realDLaws.algebra_laws a).one_mem
  change leftOperator a b x (Coeff.one b) (leftOperator a b (Coeff.one a) y v) =
    paritySign (0 * 0) • leftOperator a b
      (Coeff.mul a x (Coeff.one a)) (Coeff.mul b (Coeff.one b) y) v at h
  simpa only [zero_mul, shiftParitySign_zero, Coeff.mul_one, Coeff.one_mul, one_smul] using h

/-- Reversing those two actions produces exactly the Koszul sign. -/
theorem leftOperator_swap (a b : ZMod 8) {i j : ZMod 2} (x : Coeff a) (y : Coeff b)
    (hx : (realDData.algebra a).MemGrade i x) (hy : (realDData.algebra b).MemGrade j y)
    (v : RealCCarrier a b) :
    leftOperator a b (Coeff.one a) y (leftOperator a b x (Coeff.one b) v) =
      paritySign (j * i) • leftOperator a b x y v := by
  have h := realComputableShiftedRawDCT.laws.C.left_mul a b i j
    (Coeff.one a) x y (Coeff.one b) v hy hx
  change leftOperator a b (Coeff.one a) y (leftOperator a b x (Coeff.one b) v) =
    paritySign (j * i) • leftOperator a b
      (Coeff.mul a (Coeff.one a) x) (Coeff.mul b y (Coeff.one b)) v at h
  simpa only [Coeff.mul_one, Coeff.one_mul] using h

end RMod.BrundanEllis.Stacking.ReferenceCommutor
