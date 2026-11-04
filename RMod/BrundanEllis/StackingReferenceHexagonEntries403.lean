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

theorem left0Middle4_eq_case_0_3 : left0Middle4 0 3 = outerRightZ 4 0 3 * associatorZ 4 0 3 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle4_eq_case_0_3 : left1Middle4 0 3 = associatorZ 0 4 3 * innerLeftZ 4 0 3 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle4_eq_case_0_3 : right0Middle4 0 3 = innerRightZ 4 0 3 * associatorZ 4 0 3 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle4_eq_case_0_3 : right1Middle4 0 3 = associatorInverseZ 4 3 0 * right0Middle4 0 3 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle4_eq_case_0_3 : right2Middle4 0 3 = innerLeftZ 4 3 0 * right1Middle4 0 3 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal4_case_0_3 : ((-1 : ℤ) ^ (leftScaleBit 4 0 3).val * positiveScale (leftScaleExponent 4 0 3)) •
      (associatorZ 0 3 4 * left0Middle4 0 3) = negativeScale (leftScaleExponent 4 0 3) • (innerRightZ 0 4 3 * left1Middle4 0 3) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal4_case_0_3 : ((-1 : ℤ) ^ (rightScaleBit 4 0 3).val * positiveScale (rightScaleExponent 4 0 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 0 : ℤ)) • outerLeftZ 4 0 3 = negativeScale (rightScaleExponent 4 0 3) • (associatorZ 3 4 0 * right2Middle4 0 3) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
