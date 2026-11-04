import RMod.BrundanEllis.StackingReferenceCommutorLaws
import RMod.BrundanEllis.StackingReferenceKernelAction

/-! The certified exchange matrices act on the actual shifted real fusion
kernels. Both the inverse map and the parity are retained explicitly.
Coherence with the ternary connector is a further obligation. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

/-- The unnormalized exchange on the actual finite right-module carriers. -/
def kernelEquiv (a b : ZMod 8) : RealCCarrier a b ≃ₗ[ℝ] RealCCarrier b a :=
  (coordinates a b).trans
    ((matrixEquivOfInverse (forward a b) (inverse a b)
      (inverse_forward a b).1 (inverse_forward a b).2).trans (coordinates b a).symm)

/-- The exchange has degree `bit(a) bit(b)` in the reference's actual grading. -/
theorem kernelEquiv_grade (a b : ZMod 8) {d : ZMod 2} {v : RealCCarrier a b}
    (hv : realComputableShiftedRawDCT.data.C.MemGrade a b d v) :
    realComputableShiftedRawDCT.data.C.MemGrade b a (d + degree a b) (kernelEquiv a b v) := by
  apply (grade_iff b a _ _).mpr
  exact matrix_grade (parity a b) (parity b a) (degree a b)
    (forward a b) (matrix_parity a b).1 ((grade_iff a b d v).mp hv)

/-- The chosen inverse has the same homogeneous degree. -/
theorem kernelEquiv_symm_grade (a b : ZMod 8) {d : ZMod 2} {v : RealCCarrier b a}
    (hv : realComputableShiftedRawDCT.data.C.MemGrade b a d v) :
    realComputableShiftedRawDCT.data.C.MemGrade a b (d + degree a b)
      ((kernelEquiv a b).symm v) := by
  apply (grade_iff a b _ _).mpr
  exact matrix_grade (parity b a) (parity a b) (degree a b)
    (inverse a b) (matrix_parity a b).2 ((grade_iff b a d v).mp hv)

/-- Exchanging two degree-one kernels is odd. -/
example : degree 1 1 = 1 := rfl

/-- The same exchange is a genuine nontrivial matrix, not an identity map. -/
example : forward 1 1
    (⟨0, by change 0 < 1; omega⟩, ⟨0, by change 0 < 4; omega⟩)
    (⟨0, by change 0 < 1; omega⟩, ⟨1, by change 1 < 4; omega⟩) ≠ 0 := by decide +kernel

@[simp] theorem coordinates_kernelEquiv (a b : ZMod 8) (v : RealCCarrier a b) :
    coordinates b a (kernelEquiv a b v) =
      ((forward a b).map ((↑) : ℚ → ℝ)).mulVec (coordinates a b v) := rfl

/-- Naturality in the first input on every canonical algebra basis element. -/
theorem kernelEquiv_left_basis (a b : ZMod 8) (k : Fin (realRepDim a.val)) (v : RealCCarrier a b) :
    kernelEquiv a b (leftOperator a b (RealPChiKernel.coefficientBasis a k) (Coeff.one b) v) =
      ((-1 : ℝ) ^ (degree a b * realRepBasisParity a k).val) •
        leftOperator b a (Coeff.one b) (RealPChiKernel.coefficientBasis a k) (kernelEquiv a b v) := by
  apply (coordinates b a).injective
  rw [coordinates_kernelEquiv, leftAction_apply, map_smul, rightAction_apply, coordinates_kernelEquiv]
  simpa only [Rat.cast_pow, Rat.cast_neg, Rat.cast_one] using
    matrix_intertwiner (forward a b) (leftAction a b k) (rightAction b a k)
      ((-1 : ℚ) ^ (degree a b * realRepBasisParity a k).val)
      (left_naturality a b k) (coordinates a b v)

/-- Naturality in the second input on its canonical homogeneous basis. -/
theorem kernelEquiv_right_basis (a b : ZMod 8) (k : Fin (realRepDim b.val)) (v : RealCCarrier a b) :
    kernelEquiv a b (leftOperator a b (Coeff.one a) (RealPChiKernel.coefficientBasis b k) v) =
      ((-1 : ℝ) ^ (degree a b * realRepBasisParity b k).val) •
        leftOperator b a (RealPChiKernel.coefficientBasis b k) (Coeff.one a) (kernelEquiv a b v) := by
  apply (coordinates b a).injective
  rw [coordinates_kernelEquiv, rightAction_apply, map_smul, leftAction_apply, coordinates_kernelEquiv]
  simpa only [Rat.cast_pow, Rat.cast_neg, Rat.cast_one] using
    matrix_intertwiner (forward a b) (rightAction a b k) (leftAction b a k)
      ((-1 : ℚ) ^ (degree a b * realRepBasisParity b k).val)
      (right_naturality a b k) (coordinates a b v)

/-- First-input naturality for arbitrary homogeneous real coefficients. -/
theorem kernelEquiv_left (a b : ZMod 8) {d : ZMod 2} (x : Coeff a)
    (hx : (realDData.algebra a).MemGrade d x) (v : RealCCarrier a b) :
    kernelEquiv a b (leftOperator a b x (Coeff.one b) v) =
      ((-1 : ℝ) ^ (degree a b * d).val) •
        leftOperator b a (Coeff.one b) x (kernelEquiv a b v) := by
  apply coordinateGrade_ext (realRepBasisParity a) d
    ((kernelEquiv a b).toLinearMap.comp (firstInput a b (Coeff.one b) v))
    (((-1 : ℝ) ^ (degree a b * d).val) • secondInput b a (Coeff.one b) (kernelEquiv a b v))
      ?_ ((Coeff.component_eq_self_iff a d x).mp hx)
  intro k hk
  change kernelEquiv a b (leftOperator a b (Pi.single k 1) (Coeff.one b) v) =
    ((-1 : ℝ) ^ (degree a b * d).val) •
      leftOperator b a (Coeff.one b) (Pi.single k 1) (kernelEquiv a b v)
  rw [← coefficientBasis_single]
  simpa only [hk] using kernelEquiv_left_basis a b k v

/-- Second-input naturality for arbitrary homogeneous real coefficients. -/
theorem kernelEquiv_right (a b : ZMod 8) {d : ZMod 2} (y : Coeff b)
    (hy : (realDData.algebra b).MemGrade d y) (v : RealCCarrier a b) :
    kernelEquiv a b (leftOperator a b (Coeff.one a) y v) =
      ((-1 : ℝ) ^ (degree a b * d).val) •
        leftOperator b a y (Coeff.one a) (kernelEquiv a b v) := by
  apply coordinateGrade_ext (realRepBasisParity b) d
    ((kernelEquiv a b).toLinearMap.comp (secondInput a b (Coeff.one a) v))
    (((-1 : ℝ) ^ (degree a b * d).val) • firstInput b a (Coeff.one a) (kernelEquiv a b v))
      ?_ ((Coeff.component_eq_self_iff b d y).mp hy)
  intro k hk
  change kernelEquiv a b (leftOperator a b (Coeff.one a) (Pi.single k 1) v) =
    ((-1 : ℝ) ^ (degree a b * d).val) •
      leftOperator b a (Pi.single k 1) (Coeff.one a) (kernelEquiv a b v)
  rw [← coefficientBasis_single]
  simpa only [hk] using kernelEquiv_right_basis a b k v

/-- The full signed naturality identity, with both input coefficients arbitrary. -/
theorem kernelEquiv_naturality (a b : ZMod 8) {i j : ZMod 2} (x : Coeff a) (y : Coeff b)
    (hx : (realDData.algebra a).MemGrade i x) (hy : (realDData.algebra b).MemGrade j y)
    (v : RealCCarrier a b) :
    kernelEquiv a b (leftOperator a b x y v) =
      paritySign (degree a b * (i + j) + i * j) • leftOperator b a y x (kernelEquiv a b v) := by
  rw [← leftOperator_factor a b x y v, kernelEquiv_left a b x hx,
    kernelEquiv_right a b y hy, map_smul, leftOperator_swap b a y x hy hx]
  simp only [← paritySign_pow, smul_smul]
  rw [← shiftParitySign_add, ← shiftParitySign_add]
  congr 2
  ring


/-- The inverse exchange satisfies the same signed naturality identity. -/
theorem kernelEquiv_symm_naturality (a b : ZMod 8) {i j : ZMod 2} (x : Coeff a) (y : Coeff b)
    (hx : (realDData.algebra a).MemGrade i x) (hy : (realDData.algebra b).MemGrade j y)
    (v : RealCCarrier b a) :
    (kernelEquiv a b).symm (leftOperator b a y x v) =
      paritySign (degree a b * (i + j) + i * j) •
        leftOperator a b x y ((kernelEquiv a b).symm v) := by
  apply (kernelEquiv a b).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, kernelEquiv_naturality a b x y hx hy,
    LinearEquiv.apply_symm_apply, smul_smul, shiftParitySign_mul_self, one_smul]

end RMod.BrundanEllis.Stacking.ReferenceCommutor
