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

theorem left0Middle4_eq_case_0_2 : left0Middle4 0 2 = outerRightZ 4 0 2 * associatorZ 4 0 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle4_eq_case_0_2 : left1Middle4 0 2 = associatorZ 0 4 2 * innerLeftZ 4 0 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle4_eq_case_0_2 : right0Middle4 0 2 = innerRightZ 4 0 2 * associatorZ 4 0 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle4_eq_case_0_2 : right1Middle4 0 2 = associatorInverseZ 4 2 0 * right0Middle4 0 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle4_eq_case_0_2 : right2Middle4 0 2 = innerLeftZ 4 2 0 * right1Middle4 0 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal4_case_0_2 : ((-1 : ℤ) ^ (leftScaleBit 4 0 2).val * positiveScale (leftScaleExponent 4 0 2)) •
      (associatorZ 0 2 4 * left0Middle4 0 2) = negativeScale (leftScaleExponent 4 0 2) • (innerRightZ 0 4 2 * left1Middle4 0 2) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal4_case_0_2 : ((-1 : ℤ) ^ (rightScaleBit 4 0 2).val * positiveScale (rightScaleExponent 4 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 0 : ℤ)) • outerLeftZ 4 0 2 = negativeScale (rightScaleExponent 4 0 2) • (associatorZ 2 4 0 * right2Middle4 0 2) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
