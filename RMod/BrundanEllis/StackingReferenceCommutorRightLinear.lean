import RMod.BrundanEllis.StackingReferenceCommutor
import RMod.BrundanEllis.StackingReferenceCommutorEncoding

/-! The exchange is linear over the endpoint division algebra, not just over ℝ.
Its full coordinate matrix is identified with the matrix of left multiplications
by the coefficient vectors read on the units of the fusion rows. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

/-- Transport a coefficient vector along equality of its Brauer--Wall label. -/
def coefficientCast {a b : ZMod 8} (h : a = b) : Coeff a ≃ₗ[ℝ] Coeff b := by
  cases h
  exact LinearEquiv.refl ℝ _

@[simp] theorem coefficientCast_basis {a b : ZMod 8} (h : a = b)
    (k : Fin (realRepDim a.val)) :
    coefficientCast h (RealPChiKernel.coefficientBasis a k) =
      RealPChiKernel.coefficientBasis b (Fin.cast (congrArg (fun c : ZMod 8 => realRepDim c.val) h) k) := by
  cases h
  rfl

@[simp] theorem coefficientCast_mul {a b : ZMod 8} (h : a = b) (x y : Coeff a) :
    coefficientCast h (Coeff.mul a x y) =
      Coeff.mul b (coefficientCast h x) (coefficientCast h y) := by
  cases h
  rfl

/-- Left multiplication uses the stored division-algebra product. -/
def coefficientLeft (a : ZMod 8) (x : Coeff a) : Coeff a →ₗ[ℝ] Coeff a where
  toFun := Coeff.mul a x
  map_add' y z := by with_unfolding_all exact Coeff.mul_add a x y z
  map_smul' c y := by with_unfolding_all exact Coeff.mul_smul_right a c x y

/-- A matrix over the division algebra acts by left multiplication of each entry. -/
def coefficientOperator (a b : ZMod 8) (M : Matrix (Index b a) (Index a b) ℤ) :
    RealCCarrier a b →ₗ[ℝ] RealCCarrier b a :=
  LinearMap.pi fun r => ∑ s : FusionTable.Index a b,
    (coefficientLeft (b + a) (fun u => (coefficientZ a b M r s u.val : ℝ))).comp
      ((coefficientCast (add_comm a b)).toLinearMap.comp (LinearMap.proj s))

theorem coefficientOperator_apply (a b : ZMod 8) (M : Matrix (Index b a) (Index a b) ℤ)
    (v : RealCCarrier a b) (r : FusionTable.Index b a) :
    coefficientOperator a b M v r = ∑ s : FusionTable.Index a b,
      Coeff.mul (b + a) (fun u => (coefficientZ a b M r s u.val : ℝ))
        (coefficientCast (add_comm a b) (v s)) := by
  simp only [coefficientOperator, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  rfl

/-- On a coordinate basis vector this is exactly the certified encoding. -/
theorem coefficientOperator_basis (a b : ZMod 8) (M : Matrix (Index b a) (Index a b) ℤ)
    (r : Index b a) (s : Index a b) :
    coefficientOperator a b M ((coordinates a b).symm (Pi.single s 1)) r.1 r.2 =
      (rightLinearEncoding a b M r s : ℝ) := by
  rw [coefficientOperator_apply]
  simp_rw [coordinates_basis]
  simp only [apply_ite, map_zero]
  have hz (x : Coeff (b + a)) : Coeff.mul (b + a) x 0 = 0 := by
    with_unfolding_all exact Coeff.mul_zero (b + a) x
  simp only [hz, Finset.sum_ite_eq', Finset.mem_univ, if_true, coefficientCast_basis]
  exact (RealPChiKernel.leftMulBasisCoeff_cast (b + a) (coefficientZ a b M r.1 s.1)
    (Fin.cast (congrArg (fun c : ZMod 8 => realRepDim c.val) (add_comm a b)) s.2) r.2).symm

/-- The integer encoding is the complete coordinate matrix of the D-linear operator. -/
theorem coefficientOperator_matrix (a b : ZMod 8) (M : Matrix (Index b a) (Index a b) ℤ) :
    ((coordinates b a).toLinearMap.comp (coefficientOperator a b M)).comp
      (coordinates a b).symm.toLinearMap =
        ((rightLinearEncoding a b M).map ((↑) : ℤ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (Index a b)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  change coefficientOperator a b M ((coordinates a b).symm (Pi.single s 1)) r.1 r.2 = _
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact coefficientOperator_basis a b M r s

/-- Identify the chosen exchange with its actual division-algebra matrix. -/
theorem kernelEquiv_as_coefficientOperator (a b : ZMod 8) (v : RealCCarrier a b) :
    kernelEquiv a b v = coefficientOperator a b (forwardZ a b) v := by
  apply (coordinates b a).injective
  have h := LinearMap.congr_fun (coefficientOperator_matrix a b (forwardZ a b)) (coordinates a b v)
  change coordinates b a (coefficientOperator a b (forwardZ a b)
    ((coordinates a b).symm (coordinates a b v))) = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  rw [coordinates_kernelEquiv, h, ← (rightLinear_encoding a b).1]
  simp only [forward, Matrix.mulVecLin_apply, Matrix.map_map, Function.comp_def, Rat.cast_intCast]

/-- Each coefficient matrix commutes with right multiplication at the endpoint. -/
theorem coefficientOperator_right (a b : ZMod 8) (M : Matrix (Index b a) (Index a b) ℤ)
    (v : RealCCarrier a b) (x : Coeff (a + b)) :
    coefficientOperator a b M (realCRight a b v x) =
      realCRight b a (coefficientOperator a b M v) (coefficientCast (add_comm a b) x) := by
  funext r
  apply (Coeff.semantic (b + a)).injective
  simp only [coefficientOperator_apply, realCRight, coefficientCast_mul, map_sum, Coeff.semantic_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  exact (mul_assoc _ _ _).symm

/-- The exchange is a homogeneous map of the actual right division-algebra modules. -/
theorem kernelEquiv_right_linear (a b : ZMod 8) (v : RealCCarrier a b) (x : Coeff (a + b)) :
    kernelEquiv a b (realCRight a b v x) =
      realCRight b a (kernelEquiv a b v) (coefficientCast (add_comm a b) x) := by
  rw [kernelEquiv_as_coefficientOperator, kernelEquiv_as_coefficientOperator]
  exact coefficientOperator_right a b (forwardZ a b) v x

end RMod.BrundanEllis.Stacking.ReferenceCommutor
