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

theorem left0Middle4_eq_case_1_4 : left0Middle4 1 4 = outerRightZ 4 1 4 * associatorZ 4 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle4_eq_case_1_4 : left1Middle4 1 4 = associatorZ 1 4 4 * innerLeftZ 4 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle4_eq_case_1_4 : right0Middle4 1 4 = innerRightZ 4 1 4 * associatorZ 4 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle4_eq_case_1_4 : right1Middle4 1 4 = associatorInverseZ 4 4 1 * right0Middle4 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle4_eq_case_1_4 : right2Middle4 1 4 = innerLeftZ 4 4 1 * right1Middle4 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal4_case_1_4 : ((-1 : ℤ) ^ (leftScaleBit 4 1 4).val * positiveScale (leftScaleExponent 4 1 4)) •
      (associatorZ 1 4 4 * left0Middle4 1 4) = negativeScale (leftScaleExponent 4 1 4) • (innerRightZ 1 4 4 * left1Middle4 1 4) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal4_case_1_4 : ((-1 : ℤ) ^ (rightScaleBit 4 1 4).val * positiveScale (rightScaleExponent 4 1 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 1 : ℤ)) • outerLeftZ 4 1 4 = negativeScale (rightScaleExponent 4 1 4) • (associatorZ 4 4 1 * right2Middle4 1 4) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
