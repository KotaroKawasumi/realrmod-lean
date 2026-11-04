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

theorem left0Middle6_eq_case_7_2 : left0Middle6 7 2 = outerRightZ 6 7 2 * associatorZ 6 7 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle6_eq_case_7_2 : left1Middle6 7 2 = associatorZ 7 6 2 * innerLeftZ 6 7 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle6_eq_case_7_2 : right0Middle6 7 2 = innerRightZ 6 7 2 * associatorZ 6 7 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle6_eq_case_7_2 : right1Middle6 7 2 = associatorInverseZ 6 2 7 * right0Middle6 7 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle6_eq_case_7_2 : right2Middle6 7 2 = innerLeftZ 6 2 7 * right1Middle6 7 2 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal6_case_7_2 : ((-1 : ℤ) ^ (leftScaleBit 6 7 2).val * positiveScale (leftScaleExponent 6 7 2)) •
      (associatorZ 7 2 6 * left0Middle6 7 2) = negativeScale (leftScaleExponent 6 7 2) • (innerRightZ 7 6 2 * left1Middle6 7 2) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal6_case_7_2 : ((-1 : ℤ) ^ (rightScaleBit 6 7 2).val * positiveScale (rightScaleExponent 6 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 7 : ℤ)) • outerLeftZ 6 7 2 = negativeScale (rightScaleExponent 6 7 2) • (associatorZ 2 6 7 * right2Middle6 7 2) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
