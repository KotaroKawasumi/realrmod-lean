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

theorem left0Middle4_eq_case_1_7 : left0Middle4 1 7 = outerRightZ 4 1 7 * associatorZ 4 1 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle4_eq_case_1_7 : left1Middle4 1 7 = associatorZ 1 4 7 * innerLeftZ 4 1 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle4_eq_case_1_7 : right0Middle4 1 7 = innerRightZ 4 1 7 * associatorZ 4 1 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle4_eq_case_1_7 : right1Middle4 1 7 = associatorInverseZ 4 7 1 * right0Middle4 1 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle4_eq_case_1_7 : right2Middle4 1 7 = innerLeftZ 4 7 1 * right1Middle4 1 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal4_case_1_7 : ((-1 : ℤ) ^ (leftScaleBit 4 1 7).val * positiveScale (leftScaleExponent 4 1 7)) •
      (associatorZ 1 7 4 * left0Middle4 1 7) = negativeScale (leftScaleExponent 4 1 7) • (innerRightZ 1 4 7 * left1Middle4 1 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal4_case_1_7 : ((-1 : ℤ) ^ (rightScaleBit 4 1 7).val * positiveScale (rightScaleExponent 4 1 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 1 : ℤ)) • outerLeftZ 4 1 7 = negativeScale (rightScaleExponent 4 1 7) • (associatorZ 7 4 1 * right2Middle4 1 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
