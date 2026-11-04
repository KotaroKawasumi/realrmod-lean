import RMod.BrundanEllis.StackingReferenceCommutorRightLinear
import RMod.BrundanEllis.StackingReferenceNormalizationData

/-! Normalize the actual homogeneous division-module exchanges. Their binary
inverse, degree, signed naturality and right-linearity survive scalar rescaling.
No ternary hexagon is asserted in this module. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

/-- The chosen scalar can be inverted over the reals. -/
theorem normalizingScalar_ne_zero (a b : ZMod 8) : normalizingScalar a b ≠ 0 := by
  apply mul_ne_zero
  · split_ifs <;> norm_num
  · exact zpow_ne_zero _ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- An explicit normalization of the reference exchange. -/
def normalizedKernelEquiv (a b : ZMod 8) : RealCCarrier a b ≃ₗ[ℝ] RealCCarrier b a :=
  (kernelEquiv a b).trans
    (LinearEquiv.smulOfNeZero ℝ (RealCCarrier b a)
      (normalizingScalar a b) (normalizingScalar_ne_zero a b))

@[simp] theorem normalizedKernelEquiv_apply (a b : ZMod 8) (v : RealCCarrier a b) :
    normalizedKernelEquiv a b v = normalizingScalar a b • kernelEquiv a b v := rfl

@[simp] theorem normalizedKernelEquiv_symm_apply (a b : ZMod 8) (v : RealCCarrier b a) :
    (normalizedKernelEquiv a b).symm v =
      (kernelEquiv a b).symm ((normalizingScalar a b)⁻¹ • v) := rfl

/-- Real scalar multiplication preserves the actual kernel grading. -/
theorem kernelGrade_smul (a b : ZMod 8) (d : ZMod 2) (r : ℝ) (v : RealCCarrier a b)
    (hv : realComputableShiftedRawDCT.data.C.MemGrade a b d v) :
    realComputableShiftedRawDCT.data.C.MemGrade a b d (r • v) := by
  rw [grade_iff] at hv ⊢
  rw [map_smul]
  intro i hi
  change r * coordinates a b v i = 0
  rw [hv i hi, mul_zero]

theorem normalizedKernelEquiv_grade (a b : ZMod 8) {d : ZMod 2} (v : RealCCarrier a b)
    (hv : realComputableShiftedRawDCT.data.C.MemGrade a b d v) :
    realComputableShiftedRawDCT.data.C.MemGrade b a (d + degree a b) (normalizedKernelEquiv a b v) :=
  kernelGrade_smul b a _ _ _ (kernelEquiv_grade a b hv)

theorem normalizedKernelEquiv_symm_grade (a b : ZMod 8) {d : ZMod 2} (v : RealCCarrier b a)
    (hv : realComputableShiftedRawDCT.data.C.MemGrade b a d v) :
    realComputableShiftedRawDCT.data.C.MemGrade a b (d + degree a b)
      ((normalizedKernelEquiv a b).symm v) :=
  kernelEquiv_symm_grade a b (kernelGrade_smul b a _ _ _ hv)

/-- Rescaling retains naturality against all homogeneous input coefficients. -/
theorem normalizedKernelEquiv_naturality (a b : ZMod 8) {i j : ZMod 2} (x : Coeff a) (y : Coeff b)
    (hx : (realDData.algebra a).MemGrade i x) (hy : (realDData.algebra b).MemGrade j y)
    (v : RealCCarrier a b) :
    normalizedKernelEquiv a b (leftOperator a b x y v) =
      paritySign (degree a b * (i + j) + i * j) •
        leftOperator b a y x (normalizedKernelEquiv a b v) := by
  simp only [normalizedKernelEquiv_apply, kernelEquiv_naturality a b x y hx hy, map_smul]
  exact smul_comm _ _ _

/-- Rescaling also retains the actual right D(a+b) action. -/
theorem normalizedKernelEquiv_right_linear (a b : ZMod 8) (v : RealCCarrier a b)
    (x : Coeff (a + b)) :
    normalizedKernelEquiv a b (realCRight a b v x) =
      realCRight b a (normalizedKernelEquiv a b v) (coefficientCast (add_comm a b) x) := by
  simp only [normalizedKernelEquiv_apply, kernelEquiv_right_linear]
  exact (realCLaws.right_smul_module b a (normalizingScalar a b)
    (kernelEquiv a b v) (coefficientCast (add_comm a b) x)).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor
