import RMod.BrundanEllis.StackingReferenceInnerRightOperator
import RMod.BrundanEllis.StackingReferenceAssociatorInverse
import RMod.BrundanEllis.StackingReferenceHexagonNormalization

/-! Coordinate changes cancel along a composite diagram. Consequently the
finite coefficient hexagons imply identities of the existing reference
kernel operators. The finite equations are supplied separately by certificates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private theorem coordinate_comp {U V W U' V' W' : Type}
    [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup U'] [Module ℝ U'] [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']
    (e : U ≃ₗ[ℝ] U') (f : V ≃ₗ[ℝ] V') (g : W ≃ₗ[ℝ] W')
    (A : U →ₗ[ℝ] V) (B : V →ₗ[ℝ] W) :
    (g.toLinearMap.comp (B.comp A)).comp e.symm.toLinearMap =
      ((g.toLinearMap.comp B).comp f.symm.toLinearMap).comp
        ((f.toLinearMap.comp A).comp e.symm.toLinearMap) := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

private theorem coordinate_injective {U V U' V' : Type}
    [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup U'] [Module ℝ U'] [AddCommGroup V'] [Module ℝ V']
    (e : U ≃ₗ[ℝ] U') (f : V ≃ₗ[ℝ] V') :
    Function.Injective (fun A : U →ₗ[ℝ] V => (f.toLinearMap.comp A).comp e.symm.toLinearMap) := by
  intro A B h
  ext x
  apply f.injective
  have he := LinearMap.congr_fun h (e x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using he

private theorem integerMatrix_mul {I J K : Type} [Fintype J]
    (M : Matrix I J ℤ) (N : Matrix J K ℤ) :
    (M * N).map ((↑) : ℤ → ℝ) = M.map ((↑) : ℤ → ℝ) * N.map ((↑) : ℤ → ℝ) := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Int.cast_sum, Int.cast_mul]

/-- The first coefficient hexagon is an equality of the actual kernel operators. -/
theorem leftHexagon_operators (a b c : ZMod 8) (h : LeftEquation a b c) :
    (associatorOperator b c a).comp ((outerRightOperator a b c).comp (associatorOperator a b c)) =
      (innerRightOperator b a c).comp ((associatorOperator b a c).comp (innerLeftOperator a b c)) := by
  apply coordinate_injective (leftCoordinates a b c) (rightCoordinates b c a)
  dsimp only
  rw [coordinate_comp (leftCoordinates a b c) (leftCoordinates b c a) (rightCoordinates b c a),
    coordinate_comp (leftCoordinates a b c) (rightCoordinates a b c) (leftCoordinates b c a),
    coordinate_comp (leftCoordinates a b c) (rightCoordinates b a c) (rightCoordinates b c a),
    coordinate_comp (leftCoordinates a b c) (leftCoordinates b a c) (rightCoordinates b a c)]
  rw [associator_matrix, associator_matrix, associator_matrix,
    outerRightOperator_matrix, innerRightOperator_matrix, innerLeftOperator_matrix]
  simp only [← Matrix.mulVecLin_mul]
  apply congrArg Matrix.mulVecLin
  simpa only [leftShortZ, leftLongZ, integerMatrix_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.mul_assoc, mul_assoc, mul_comm, mul_left_comm] using leftHexagon_normalized a b c h

private theorem coordinate_smul {U V U' V' : Type}
    [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup U'] [Module ℝ U'] [AddCommGroup V'] [Module ℝ V']
    (e : U ≃ₗ[ℝ] U') (f : V ≃ₗ[ℝ] V') (r : ℝ) (A : U →ₗ[ℝ] V) :
    (f.toLinearMap.comp (r • A)).comp e.symm.toLinearMap =
      r • ((f.toLinearMap.comp A).comp e.symm.toLinearMap) := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul]

private theorem mulVecLin_smul {I J : Type} [Fintype J] (r : ℝ) (M : Matrix I J ℝ) :
    (r • M).mulVecLin = r • M.mulVecLin := by
  ext v i
  simp only [Matrix.mulVecLin_apply, LinearMap.smul_apply, Matrix.smul_mulVec, Pi.smul_apply]

/-- The second coefficient hexagon gives precisely the stated quadratic sign. -/
theorem rightHexagon_operators (a b c : ZMod 8) (h : RightEquation a b c) :
    outerLeftOperator a b c = paritySign (rightDefect a b c) •
      (associatorOperator c a b).comp ((innerLeftOperator a c b).comp
        ((associatorInverseOperator a c b).comp
          ((innerRightOperator a b c).comp (associatorOperator a b c)))) := by
  have hi : realTInverseScale a c b * (RMod.ConstructiveConnectorTable.inverseScale a c b : ℝ) = 1 := by
    norm_num [realTInverseScale, RMod.ConstructiveConnectorTable.inverseScale_ne_zero]
  have hm := congrArg (fun M : Matrix (RightIndex c a b) (LeftIndex a b c) ℝ =>
    realTInverseScale a c b • M) (rightHexagon_normalized a b c h)
  simp only [smul_smul] at hm
  have hc : realTInverseScale a c b *
      ((RMod.ConstructiveConnectorTable.inverseScale a c b : ℝ) * normalizingScalar (a + b) c) =
      normalizingScalar (a + b) c := by
    rw [← mul_assoc, hi, one_mul]
  rw [hc] at hm
  apply coordinate_injective (leftCoordinates a b c) (rightCoordinates c a b)
  dsimp only
  rw [coordinate_smul, outerLeftOperator_matrix,
    coordinate_comp (leftCoordinates a b c) (leftCoordinates c a b) (rightCoordinates c a b),
    coordinate_comp (leftCoordinates a b c) (leftCoordinates a c b) (leftCoordinates c a b),
    coordinate_comp (leftCoordinates a b c) (rightCoordinates a c b) (leftCoordinates a c b),
    coordinate_comp (leftCoordinates a b c) (rightCoordinates a b c) (rightCoordinates a c b)]
  rw [associator_matrix, associator_matrix, innerLeftOperator_matrix,
    associatorInverse_matrix, innerRightOperator_matrix]
  simp only [← Matrix.mulVecLin_mul, ← mulVecLin_smul]
  apply congrArg Matrix.mulVecLin
  simpa only [rightLongZ, integerMatrix_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.mul_assoc, mul_assoc, mul_comm, mul_left_comm] using hm

end RMod.BrundanEllis.Stacking.ReferenceCommutor
