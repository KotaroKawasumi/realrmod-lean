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

theorem left0Middle6_eq_case_7_4 : left0Middle6 7 4 = outerRightZ 6 7 4 * associatorZ 6 7 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle6_eq_case_7_4 : left1Middle6 7 4 = associatorZ 7 6 4 * innerLeftZ 6 7 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle6_eq_case_7_4 : right0Middle6 7 4 = innerRightZ 6 7 4 * associatorZ 6 7 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle6_eq_case_7_4 : right1Middle6 7 4 = associatorInverseZ 6 4 7 * right0Middle6 7 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle6_eq_case_7_4 : right2Middle6 7 4 = innerLeftZ 6 4 7 * right1Middle6 7 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal6_case_7_4 : ((-1 : ℤ) ^ (leftScaleBit 6 7 4).val * positiveScale (leftScaleExponent 6 7 4)) •
      (associatorZ 7 4 6 * left0Middle6 7 4) = negativeScale (leftScaleExponent 6 7 4) • (innerRightZ 7 6 4 * left1Middle6 7 4) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal6_case_7_4 : ((-1 : ℤ) ^ (rightScaleBit 6 7 4).val * positiveScale (rightScaleExponent 6 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 4 7 : ℤ)) • outerLeftZ 6 7 4 = negativeScale (rightScaleExponent 6 7 4) • (associatorZ 4 6 7 * right2Middle6 7 4) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
