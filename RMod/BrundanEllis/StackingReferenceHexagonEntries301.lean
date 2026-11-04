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

theorem left0Middle3_eq_case_0_1 : left0Middle3 0 1 = outerRightZ 3 0 1 * associatorZ 3 0 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle3_eq_case_0_1 : left1Middle3 0 1 = associatorZ 0 3 1 * innerLeftZ 3 0 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle3_eq_case_0_1 : right0Middle3 0 1 = innerRightZ 3 0 1 * associatorZ 3 0 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle3_eq_case_0_1 : right1Middle3 0 1 = associatorInverseZ 3 1 0 * right0Middle3 0 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle3_eq_case_0_1 : right2Middle3 0 1 = innerLeftZ 3 1 0 * right1Middle3 0 1 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal3_case_0_1 : ((-1 : ℤ) ^ (leftScaleBit 3 0 1).val * positiveScale (leftScaleExponent 3 0 1)) •
      (associatorZ 0 1 3 * left0Middle3 0 1) = negativeScale (leftScaleExponent 3 0 1) • (innerRightZ 0 3 1 * left1Middle3 0 1) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal3_case_0_1 : ((-1 : ℤ) ^ (rightScaleBit 3 0 1).val * positiveScale (rightScaleExponent 3 0 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 0 : ℤ)) • outerLeftZ 3 0 1 = negativeScale (rightScaleExponent 3 0 1) • (associatorZ 1 3 0 * right2Middle3 0 1) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
