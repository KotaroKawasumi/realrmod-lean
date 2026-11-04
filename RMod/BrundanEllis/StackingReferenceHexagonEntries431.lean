import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
open Superfusion

theorem left0Middle4_eq_case_3_1 : left0Middle4 3 1 = outerRightZ 4 3 1 * associatorZ 4 3 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle4_eq_case_3_1 : left1Middle4 3 1 = associatorZ 3 4 1 * innerLeftZ 4 3 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle4_eq_case_3_1 : right0Middle4 3 1 = innerRightZ 4 3 1 * associatorZ 4 3 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle4_eq_case_3_1 : right1Middle4 3 1 = associatorInverseZ 4 1 3 * right0Middle4 3 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle4_eq_case_3_1 : right2Middle4 3 1 = innerLeftZ 4 1 3 * right1Middle4 3 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal4_case_3_1 : ((-1 : ℤ) ^ (leftScaleBit 4 3 1).val * positiveScale (leftScaleExponent 4 3 1)) •
      (associatorZ 3 1 4 * left0Middle4 3 1) = negativeScale (leftScaleExponent 4 3 1) • (innerRightZ 3 4 1 * left1Middle4 3 1) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal4_case_3_1 : ((-1 : ℤ) ^ (rightScaleBit 4 3 1).val * positiveScale (rightScaleExponent 4 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 1 3 : ℤ)) • outerLeftZ 4 3 1 = negativeScale (rightScaleExponent 4 3 1) • (associatorZ 1 4 3 * right2Middle4 3 1) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
