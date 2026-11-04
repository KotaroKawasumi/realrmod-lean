import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
open Superfusion

theorem left0Middle6_eq_case_2_0 : left0Middle6 2 0 = outerRightZ 6 2 0 * associatorZ 6 2 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle6_eq_case_2_0 : left1Middle6 2 0 = associatorZ 2 6 0 * innerLeftZ 6 2 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle6_eq_case_2_0 : right0Middle6 2 0 = innerRightZ 6 2 0 * associatorZ 6 2 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle6_eq_case_2_0 : right1Middle6 2 0 = associatorInverseZ 6 0 2 * right0Middle6 2 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle6_eq_case_2_0 : right2Middle6 2 0 = innerLeftZ 6 0 2 * right1Middle6 2 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal6_case_2_0 : ((-1 : ℤ) ^ (leftScaleBit 6 2 0).val * positiveScale (leftScaleExponent 6 2 0)) •
      (associatorZ 2 0 6 * left0Middle6 2 0) = negativeScale (leftScaleExponent 6 2 0) • (innerRightZ 2 6 0 * left1Middle6 2 0) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal6_case_2_0 : ((-1 : ℤ) ^ (rightScaleBit 6 2 0).val * positiveScale (rightScaleExponent 6 2 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 0 2 : ℤ)) • outerLeftZ 6 2 0 = negativeScale (rightScaleExponent 6 2 0) • (associatorZ 0 6 2 * right2Middle6 2 0) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
