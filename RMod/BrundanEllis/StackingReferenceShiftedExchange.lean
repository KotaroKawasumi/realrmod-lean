import RMod.BrundanEllis.StackingReferenceNormalization
import Superfusion.RMod.FromRawDCT.Tensor

/-! Endpoint parity shifts contribute a specific scalar to the reference
exchange. Its signed naturality is proved against the actual raw tensor
operator, retaining the distinction between morphism degree and coefficient degree. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Endpoint shifts change the exchange by this Koszul exponent. -/
def exchangeShift (a b : ZMod 8) (p q : ZMod 2) : ZMod 2 := degree a b * (p + q) + p * q

/-- The actual tensor operator on fusion rows for shifted source/target atoms. -/
def shiftedTensorOperator (a b : ZMod 8) (p q q' : ZMod 2) (x : Coeff a) (y : Coeff b) :
    RealCCarrier a b →ₗ[ℝ] RealCCarrier a b :=
  paritySign (p * (q + q')) •
    leftOperator a b (routeRowTwist realDData a q' x) (routeRowTwist realDData b p y)

/-- The chosen exchange on shifted fusion rows. -/
def shiftedExchange (a b : ZMod 8) (p q : ZMod 2) :
    RealCCarrier a b →ₗ[ℝ] RealCCarrier b a :=
  paritySign (exchangeShift a b p q) • (normalizedKernelEquiv a b).toLinearMap

private theorem rowTwist_homogeneous (a : ZMod 8) (p d : ZMod 2) (x : Coeff a)
    (hx : (realDData.algebra a).MemGrade d x) :
    routeRowTwist realDData a p x = paritySign (p * d) • x := by
  exact routeRowTwist_of_memGrade (realDData.algebra a) (realDLaws.algebra_laws a) p d x hx

private theorem leftOperator_smul_inputs (a b : ZMod 8) (r s : ℝ) (x : Coeff a) (y : Coeff b)
    (v : RealCCarrier a b) :
    leftOperator a b (r • x) (s • y) v = (r * s) • leftOperator a b x y v := by
  have hleft : leftOperator a b (r • x) (s • y) v =
      r • leftOperator a b x (s • y) v :=
    realComputableShiftedRawDCT.laws.C.left_smul_left a b r x (s • y) v
  have hright : leftOperator a b x (s • y) v = s • leftOperator a b x y v :=
    realComputableShiftedRawDCT.laws.C.left_smul_right a b s x y v
  rw [hleft, hright, smul_smul]

/-- Homogeneous atomic coefficients reduce the stored tensor operator to a scalar times C.left. -/
theorem shiftedTensorOperator_homogeneous (a b : ZMod 8) (p p' q q' i j : ZMod 2)
    (x : Coeff a) (y : Coeff b)
    (hx : (realDData.algebra a).MemGrade (i + p + p') x)
    (hy : (realDData.algebra b).MemGrade (j + q + q') y) (v : RealCCarrier a b) :
    shiftedTensorOperator a b p q q' x y v =
      paritySign (q' * (i + p + p') + p * j) • leftOperator a b x y v := by
  simp only [shiftedTensorOperator, LinearMap.smul_apply,
    rowTwist_homogeneous a q' _ x hx, rowTwist_homogeneous b p _ y hy,
    leftOperator_smul_inputs, smul_smul, ← shiftParitySign_add]
  congr 2
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, show (3 : ZMod 2) = 1 from rfl,
    mul_zero, mul_one, zero_add]

/-- The endpoint correction makes the naturality sign depend on morphism degrees. -/
theorem shiftedExchange_naturality (a b : ZMod 8) (p p' q q' i j : ZMod 2)
    (x : Coeff a) (y : Coeff b)
    (hx : (realDData.algebra a).MemGrade (i + p + p') x)
    (hy : (realDData.algebra b).MemGrade (j + q + q') y) (v : RealCCarrier a b) :
    shiftedExchange a b p' q' (shiftedTensorOperator a b p q q' x y v) =
      paritySign (degree a b * (i + j) + i * j) •
        shiftedTensorOperator b a q p p' y x (shiftedExchange a b p q v) := by
  rw [shiftedTensorOperator_homogeneous a b p p' q q' i j x y hx hy,
    shiftedTensorOperator_homogeneous b a q q' p p' j i y x hy hx]
  simp only [shiftedExchange, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul,
    normalizedKernelEquiv_naturality a b x y hx hy, smul_smul, ← shiftParitySign_add]
  congr 2
  unfold exchangeShift
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, show (3 : ZMod 2) = 1 from rfl,
    mul_zero, mul_one, add_zero, zero_add]


/-- Evaluation on a row unit reads the actual stored left coefficient. -/
theorem leftOperator_unit_column (a b : ZMod 8) (x : Coeff a) (y : Coeff b)
    (source target : FusionTable.Index a b) :
    leftOperator a b x y (Pi.single source (Coeff.one (a + b))) target =
      (shiftCData realDData realCData realComputableNuBeta.data).leftCoeff a b target source x y := by
  change (List.ofFn fun r : FusionTable.Index a b => Coeff.mul (a + b)
    (FusionTable.fusionCoefficient a b target r
      (routeRowTwist realDData a (shiftNu realComputableNuBeta.data a b) x)
      (routeRowTwist realDData b (shiftNu realComputableNuBeta.data a b) y))
    ((Pi.single source (Coeff.one (a + b)) : RealCCarrier a b) r)).sum = _
  rw [List.sum_ofFn]
  have hz (z : Coeff (a + b)) : Coeff.mul (a + b) z 0 = 0 := by
    with_unfolding_all exact Coeff.mul_zero (a + b) z
  simp only [Pi.single_apply, apply_ite, hz, Coeff.mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rfl

/-- Every matrix column is exactly the raw tensor coefficient, including the shift signs. -/
theorem shiftedTensorOperator_unit_column (a b : ZMod 8) (p q q' : ZMod 2)
    (x : Coeff a) (y : Coeff b) (source target : FusionTable.Index a b) :
    shiftedTensorOperator a b p q q' x y (Pi.single source (Coeff.one (a + b))) target =
      Tensor.coefficient realDData (shiftCData realDData realCData realComputableNuBeta.data)
        a b p q q' source target x y := by
  change paritySign (p * (q + q')) •
    (leftOperator a b (routeRowTwist realDData a q' x) (routeRowTwist realDData b p y)
      (Pi.single source (Coeff.one (a + b))) target) = _
  rw [leftOperator_unit_column]
  rfl

/-- Shifting the first odd atom reverses an odd/odd crossing sign. -/
example : exchangeShift 1 1 1 0 = 1 := rfl

/-- Two odd endpoint shifts cancel that degree contribution but retain their Koszul sign. -/
example : exchangeShift 1 1 1 1 = 1 := rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
