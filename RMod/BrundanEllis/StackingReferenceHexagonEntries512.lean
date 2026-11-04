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

theorem left0Middle5_eq_case_1_2 : left0Middle5 1 2 = outerRightZ 5 1 2 * associatorZ 5 1 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle5_eq_case_1_2 : left1Middle5 1 2 = associatorZ 1 5 2 * innerLeftZ 5 1 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle5_eq_case_1_2 : right0Middle5 1 2 = innerRightZ 5 1 2 * associatorZ 5 1 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle5_eq_case_1_2 : right1Middle5 1 2 = associatorInverseZ 5 2 1 * right0Middle5 1 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle5_eq_case_1_2 : right2Middle5 1 2 = innerLeftZ 5 2 1 * right1Middle5 1 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal5_case_1_2 : ((-1 : ℤ) ^ (leftScaleBit 5 1 2).val * positiveScale (leftScaleExponent 5 1 2)) •
      (associatorZ 1 2 5 * left0Middle5 1 2) = negativeScale (leftScaleExponent 5 1 2) • (innerRightZ 1 5 2 * left1Middle5 1 2) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal5_case_1_2 : ((-1 : ℤ) ^ (rightScaleBit 5 1 2).val * positiveScale (rightScaleExponent 5 1 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 1 : ℤ)) • outerLeftZ 5 1 2 = negativeScale (rightScaleExponent 5 1 2) • (associatorZ 2 5 1 * right2Middle5 1 2) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
