import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
open Superfusion

theorem left0Middle5_eq_case_1_0 : left0Middle5 1 0 = outerRightZ 5 1 0 * associatorZ 5 1 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle5_eq_case_1_0 : left1Middle5 1 0 = associatorZ 1 5 0 * innerLeftZ 5 1 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle5_eq_case_1_0 : right0Middle5 1 0 = innerRightZ 5 1 0 * associatorZ 5 1 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle5_eq_case_1_0 : right1Middle5 1 0 = associatorInverseZ 5 0 1 * right0Middle5 1 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle5_eq_case_1_0 : right2Middle5 1 0 = innerLeftZ 5 0 1 * right1Middle5 1 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal5_case_1_0 : ((-1 : ℤ) ^ (leftScaleBit 5 1 0).val * positiveScale (leftScaleExponent 5 1 0)) •
      (associatorZ 1 0 5 * left0Middle5 1 0) = negativeScale (leftScaleExponent 5 1 0) • (innerRightZ 1 5 0 * left1Middle5 1 0) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal5_case_1_0 : ((-1 : ℤ) ^ (rightScaleBit 5 1 0).val * positiveScale (rightScaleExponent 5 1 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 1 : ℤ)) • outerLeftZ 5 1 0 = negativeScale (rightScaleExponent 5 1 0) • (associatorZ 0 5 1 * right2Middle5 1 0) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
