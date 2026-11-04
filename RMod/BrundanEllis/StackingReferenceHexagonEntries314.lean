import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
open Superfusion

theorem left0Middle3_eq_case_1_4 : left0Middle3 1 4 = outerRightZ 3 1 4 * associatorZ 3 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle3_eq_case_1_4 : left1Middle3 1 4 = associatorZ 1 3 4 * innerLeftZ 3 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle3_eq_case_1_4 : right0Middle3 1 4 = innerRightZ 3 1 4 * associatorZ 3 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle3_eq_case_1_4 : right1Middle3 1 4 = associatorInverseZ 3 4 1 * right0Middle3 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle3_eq_case_1_4 : right2Middle3 1 4 = innerLeftZ 3 4 1 * right1Middle3 1 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal3_case_1_4 : ((-1 : ℤ) ^ (leftScaleBit 3 1 4).val * positiveScale (leftScaleExponent 3 1 4)) •
      (associatorZ 1 4 3 * left0Middle3 1 4) = negativeScale (leftScaleExponent 3 1 4) • (innerRightZ 1 3 4 * left1Middle3 1 4) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal3_case_1_4 : ((-1 : ℤ) ^ (rightScaleBit 3 1 4).val * positiveScale (rightScaleExponent 3 1 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 1 : ℤ)) • outerLeftZ 3 1 4 = negativeScale (rightScaleExponent 3 1 4) • (associatorZ 4 3 1 * right2Middle3 1 4) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
